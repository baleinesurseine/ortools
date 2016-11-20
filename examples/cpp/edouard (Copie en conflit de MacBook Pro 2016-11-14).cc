#include <cstdio>
#include <fstream>
#include <iostream>
#include "base/commandlineflags.h"
#include "base/split.h"
#include "base/logging.h"
#include "base/filelinereader.h"
#include "base/stringprintf.h"
#include "constraint_solver/constraint_solver.h"
#include "util/json.hpp"

// Want to say Hello ? contact <base64>ZWRvdWFyZC5maWNoZXJAZ21haWwuY29t

// for convenience
using json = nlohmann::json;

DEFINE_string(input, "", "");
DEFINE_string(solution, "", "");

namespace operations_research {

int tb(int id1, int id2);

  class Model {
  public:

    std::map<std::pair<int, int>, int> travel;

    explicit Model(const std::string& modelname, int min_time, int max_time) : solv(modelname) {
      min_t = min_time;
      max_t = max_time;
    }

    void createConstraints() {

      // 0.a - Create optimized meetings
      for (auto const& obj : opt_dur) {
        int key = obj.first;
        int dur = obj.second;
        IntVar* dr = solv.MakeIntVar(min_t, max_t);
        d.insert(std::make_pair(key, dr));
        IntervalVar* sr = solv.MakeFixedDurationIntervalVar(dr, dur, task_names[key]);
        s.insert(std::make_pair(key, sr));
      }
      // 0.b - Create fixed meetings
      for (auto const& obj : fixed_dur) {
        int key = obj.first;
        int dur = obj.second;
        int start = fixed_start[key];
        IntervalVar* sr = solv.MakeFixedInterval(start, dur, task_names[key]);
        s.insert(std::make_pair(key, sr));
      }

      // 1 - Début de la réunion après la date au plus tôt
      for (auto const& obj : opt_after) {
        int key = obj.first;
        int after = obj.second;
        IntExpr* delr = solv.MakeDifference(after, d[key]);
        solv.MakeLessOrEqual(delr, 0); // CHECK if correct direction of comparison
      }

      // 2 - Calcul du nombre de personnes par site pour une réunion
      // 2.a - Initialisation de e_r,l
      int nb_pers = people_names.size(); // count number of persons
      for (auto const& obj1 : s) { // loop on all tasks
        int task = obj1.first;
        for (auto const& obj2 : location_names) { // loop on all locations
          int loc = obj2.first;
          IntVar* erl = solv.MakeIntVar(0, nb_pers);
          e.insert(std::make_pair(std::make_pair(task, loc), erl));
        }
      }
      // 2.b - Initialisation de l_p,r
      std::vector<int> all_loc; // list of all locations
      for (auto const& obj : location_names) {
        int key = obj.first;
        all_loc.push_back(key);
      }
      for (auto const& obj : s) { // loop on all tasks
        int key = obj.first;
        std::vector<int> parts = participants[key];
        if (opt_dur.find(key) != opt_dur.end()) { // optimized task
          for (auto const& part : parts) {
            IntVar* lpr = solv.MakeIntVar(all_loc); // initial domain is all locations
            l.insert(std::make_pair(std::make_pair(part, key), lpr));
          }
        } else { // fixed task
          int loc = fixed_loc[key];
          for (auto const& part : parts) {
            IntVar* lpr = solv.MakeIntVar(loc, loc); // initial domain is singleton
            l.insert(std::make_pair(std::make_pair(part, key), lpr));
          }
        }
      }
      // 2.c - Calcul
      for (auto const& obj1 : s) { // loop on all tasks
        int task = obj1.first;
        std::vector<int> parts = participants[task]; // participants of task
        std::vector<IntVar*> lprs; // list of participants to task
        for (auto const& part : parts) {
          IntVar* lpr = l[std::make_pair(part, task)];
          lprs.push_back(lpr);
        }
        for (auto const& obj3 : location_names) { // loop on all locations
          int loc = obj3.first;
          solv.MakeCount(lprs, loc, e[std::make_pair(task, loc)]);
        }
      }
      // 3 - Au plus une salle par site pour une même réunion
      // 3.a - Init booleans a_s,r
      for (auto const& obj1 : room_names) {
        int room = obj1.first;
        for (auto const& obj2 : task_names) {
          int task = obj2.first;
          IntVar* asr = solv.MakeBoolVar();
          a.insert(std::make_pair(std::make_pair(room, task),asr));
        }
      }
      // 3.b - Add constraints
      // 4 - Capacité de la salle de réunion
      for (auto const& obj1 : s) {
        int task = obj1.first;
        for (auto const& obj2 : location_names) {
          int loc = obj2.first;
          std::vector<IntVar*> asrl;
          std::vector<int> caprl;
          std::vector<int> sl = salles[loc];
          for (auto const& salle : sl) {
            asrl.push_back(a[std::make_pair(salle, task)]);
            caprl.push_back(capacity[salle]);
          }
          solv.MakeSumLessOrEqual(asrl, 1);
          asrl.push_back(e[std::make_pair(task, loc)]);
          caprl.push_back(-1);
          solv.MakeScalProdGreaterOrEqual(asrl, caprl, 0);
        }
      }
      // 5 - Au plus une réunion par salle à tout instant
      for (auto const& obj1 : room_names) {
        int salle = obj1.first;
        std::vector<IntVar*> asr;
        std::vector<IntervalVar*> sr;
        for (auto const& obj2 : s) {
          int task = obj2.first;
          asr.push_back(a[std::make_pair(salle, task)]);
          sr.push_back(s[task]);
        }
        solv.MakeCumulative(sr, asr, 1, "capacité salle");
      }
      // 6 - Détection du multisite de chaque réunion
      int ll = (location_names.begin())->first; // lowest location id
      int ul = (--location_names.end())->first; // highest location id
      for (auto const& obj1 : s) {
        int task = obj1.first;
        IntVar* lb = solv.MakeIntVar(ll, ul);
        IntVar* ub = solv.MakeIntVar(ll, ul);
        IntVar* mr = solv.MakeBoolVar();
        m.insert(std::make_pair(task, mr));
        std::vector<IntVar*> lpr;
        for (auto const& part : participants[task]) {
          lpr.push_back(l[std::make_pair(part, task)]);
        }
        solv.MakeMinEquality(lpr, lb);
        solv.MakeMaxEquality(lpr, ub);
        solv.MakeIsDifferentCt(lb, ub, mr);
      }
      // 7 - Visio dans chaque salle si multisite
      for (auto const& obj1 : s) {
        int task = obj1.first;
        std::vector<IntVar*> asr; // non-visio rooms used for task
        for (auto const& room : non_viso) {
          asr.push_back(a[std::make_pair(room, task)]);
        }
        solv.MakeEquality(solv.MakeProd(m[task],solv.MakeSum(asr)), 0);
      }
      // 8 - Temps de trajet
      int rl = (task_names.begin())->first; // lowest task index
      int ru = (--task_names.end())->first; // highest task index

      for (auto const& obj1 : people_names) { // loop on people
        int people = obj1.first;
        std::vector<int> tasks = meetings[people];
        std::vector<IntVar*> dr; // starting times of people's tasks
        std::vector<int> tr; // durations of people's tasks
        std::vector<IntVar*> lr; // locationIds of people's tasks
        std::vector<IntVar*> dspq; // sorted starting times of people's tasks

        int q = 0;
        for (auto const& task : tasks) { // loop on people's tasks
          dr.push_back(d[task]);
          tr.push_back(durations[task]);
          lr.push_back(l[std::make_pair(people, task)]);
          IntVar* ds_pq = solv.MakeIntVar(min_t, max_t);
          ds.insert(std::make_pair(std::make_pair(people, q++), ds_pq));
          dspq.push_back(ds_pq);
        }
        int nbq = q;
        cout << "People: " << obj1.second << " ; q: " << nbq << "\n";
        solv.MakeSortingConstraint(dr, dspq); // ds_pq est l'heure de début de la q_ième réunion de p

        for (q=0; q < nbq; q++) {
          IntVar* i_pq = solv.MakeIntVar(rl, ru);
          IntVar* ds_pq = ds[std::make_pair(people, q)];
          solv.MakeElementEquality(dr, i_pq, ds_pq);
          IntExpr* f_pq = solv.MakeSum(ds_pq, solv.MakeElement(tr, i_pq));
          f.insert(std::make_pair(std::make_pair(people, q), f_pq));
          IntExpr* ls_pq = solv.MakeElement(lr, i_pq);
          ls.insert(std::make_pair(std::make_pair(people, q), ls_pq));
        }

        for (q=0; q < nbq - 1; q++) {
          IntVar* ls_pq = ls[std::make_pair(people, q)]->Var();
          IntVar* ls_pqp = ls[std::make_pair(people, q+1)]->Var();
          IntExpr* tr_pq = solv.MakeElement(tb, ls_pq, ls_pqp);
          IntExpr* f_pq = f[std::make_pair(people, q)];
          IntExpr* z_pq = solv.MakeSum(f_pq, tr_pq);
          z.insert(std::make_pair(std::make_pair(people, q), z_pq));
          solv.MakeLessOrEqual(z_pq, ds[std::make_pair(people, q+1)]);
        }
      }

      // 9 - Plages de temps non travaillées

      // 10 - Les réunions où p n’est pas présente ne doivent pas se tenir dans un bureau affecté à p

      // 11 - Tâches à un seul participant
    }



    void Load(std::istream& iStr, std::ostream& oStr) {

      json j;
      iStr >> j;

      oStr << parseLocations(j) << " location(s)\n";
      oStr << parseRooms(j) << " room(s)\n";
      oStr << parseCalendars(j) << " calendar(s)\n";
      oStr << parsePeople(j) << " people\n";
      oStr << parseTasks(j) << " task(s)\n";
      oStr << parseDistances(j) << " distance(s)\n";
    }

  private:

    int min_t;
    int max_t;

    // contraint Solver
    Solver solv;
    std::map<int, IntervalVar*> s; // <task_id, s_r>
    std::map<int, IntVar*> d; // <task_id, d_r>
    std::map<std::pair<int, int>, IntVar*> ds; // debut réunions triées par heures croissantes
    std::map<int, IntVar*> m; // <task_id, m_r>
    std::map<std::pair<int, int>, IntVar*> l; //<(people_id, task_id), l_p,r>
    std::map<std::pair<int, int>, IntVar*> a; // <(room_id, task_id), a_s,r>
    std::map<std::pair<int, int>, IntVar*> e; // <(task_id, loc_id), e_r,l>
    std::map<int, std::vector<IntervalVar*>> o; // <people_id; [o_p,k]>
    std::map<std::pair<int, int>, IntExpr*> ls;
    std::map<std::pair<int, int>, IntExpr*> z;
    std::map<std::pair<int, int>, IntExpr*> f;

    // données de référentiel
    std::map<int, std::string> task_names;
    std::map<int, std::string> people_names;
    std::map<int, std::string> location_names;
    std::map<int, std::string> room_names;

    // données du problème de programmation par contraintes
    std::map<int, int> durations;
    std::map<int, int> opt_dur; // <task_id, duration> durée des réunions à optimiser
    std::map<int, int> opt_after; // <task_id, date au plus tôt> heure au plus tôt pour les réunions à optimiser
    std::map<int, int> fixed_start; // <task_id, start> heure de début des réunions fixées
    std::map<int, int> fixed_dur; // <task_id, duration> durée des réunions fixées
    std::map<int, int> fixed_loc; // <task_id, locationId> lieux des réunions fixées
    std::map<int, int> fixed_room; // <task_id, roomId> salle des réunions fixées  USEFUL ?
    std::map<int, std::vector<int>> participants; // <task_id, [peopleId]> participants à une réunion
    std::map<int, std::vector<int>> salles; // <location_id, [room_Id]> salles d'un site
    std::map<int, int> site_salle; // <room_Id, location_id> site d'une salle
    std::map<int, int> capacity; // <room_id, capacity> capacité des salles
    std::vector<int> non_viso; // <roomId> liste des salles sans visio
    std::map<int, std::vector<int>> meetings; // <peopleId, [task_id]> liste des réunions d'une personne
    std::map<int, std::vector<int>> solo; // <peopleId, [task_id]> liste des tâches solo d'une personne
    std::map<int, std::vector<int>> start_off; // <calId, [start]> début des plages non travaillées d'un calendrier
    std::map<int, std::vector<int>> duration_off; // <calId, [duration]> durée des plages non travaillées d'un calendrier
    std::map<int, std::vector<int>> fixed_zero; // <calId, [start]> tâches fixées de durée 0 dans le calendrier
    std::map<int, std::vector<int>> off_calendars; // <peopleId, [calId]> calendrier de congés d'une personne

    int parseLocations(json j) {
      if (j.find("locations") == j.end()) { // nothing to parse
        return -1;
      }

      json locs = j["locations"];
      int numLocs = locs.size();

      for (auto const& obj : locs) {
        int id = obj["id"];
        std::string name =  obj["name"];
        location_names.insert(std::make_pair(id, name));
        std::vector<int> empty = {};
        salles.insert(std::make_pair(id, empty));

        std::cout << id << " : " << name << "\n";
      }
      return numLocs;
    }

    int parsePeople(json j) {
      if (j.find("people") == j.end()) { // nothing to parse
        return -1;
      }
      json people = j["people"]; //   {"id": 0, "name": "Edouard Fischer", "workplaceId": 0, "calendars": [42]}
      int numPeople = people.size();

      int zero_task_id = 10000;

      for (auto const& obj : people) {
        int id = obj["id"];
        std::vector<int> un_part = {id};
        std::string name =  obj["name"];
        int wpId = obj["workplaceId"];
        std::vector<int> calIds = obj["calendars"];
        std::vector<int> empty = {};
        people_names.insert(std::make_pair(id, name));
        meetings.insert(std::make_pair(id, empty));
        solo.insert(std::make_pair(id, empty));
        off_calendars.insert(std::make_pair(id, calIds));

        // calendars - zero lenght tasks
        for (auto const& calId : calIds) {
          std::vector<int> fixedIds = fixed_zero[calId];
          for (auto const& zero_start : fixedIds) {
            fixed_start.insert(std::make_pair(zero_task_id, zero_start));
            fixed_dur.insert(std::make_pair(zero_task_id, 0));
            durations.insert(std::make_pair(zero_task_id, 0));
            fixed_room.insert(std::make_pair(zero_task_id, wpId));
            fixed_loc.insert(std::make_pair(zero_task_id, site_salle[wpId]));
            participants.insert(std::make_pair(zero_task_id, un_part));
            meetings[id].push_back(zero_task_id);
            zero_task_id++;
          }
        }

        std::cout << id << " : " << name << " ; wp = " << wpId << " ; #cals = " << calIds.size() << "\n";
      }
      return numPeople;
    }

    int parseTasks(json j) {
      if (j.find("locations") == j.end()) { // nothing to parse
        return -1;
      }

      json tasks = j["tasks"];
      int numTasks = tasks.size();

      for (auto const& obj : tasks) {
        int id = obj["id"];
        std::string name =  obj["name"];
        std::vector<int> membIds = obj["members"];
        int duration = obj["duration"];

        task_names.insert(std::make_pair(id, name));
        participants.insert(std::make_pair(id, membIds));
        for (auto const& it1 : membIds) {
          meetings[it1].push_back(id);
        }
        if (membIds.size() == 1) {
          solo[membIds.front()].push_back(id);
        }

        int start = -1;
        int locId = -1;
        int roomId = -1;
        int after = -1;
        if (obj.find("start") == obj.end()) // réunion à optimiser
        {
          opt_dur.insert(std::make_pair(id, duration));
          durations.insert(std::make_pair(id, duration));
          after = obj["after"];
          opt_after.insert(std::make_pair(id, after));
        } else { // réunion fixée
          start = obj["start"];
          locId = obj["location"];
          roomId = obj["room"];
          fixed_start.insert(std::make_pair(id, start));
          fixed_dur.insert(std::make_pair(id, duration));
          durations.insert(std::make_pair(id, duration));
          fixed_loc.insert(std::make_pair(id, locId));
          fixed_room.insert(std::make_pair(id, roomId));
        }

        std::cout << id << " : " << name << " ; loc = " << locId << " ; duration = " << duration << " ; #members = " << membIds.size() << "\n";
      }
      return numTasks;
    }

    int parseCalendars(json j) {
      if (j.find("calendars") == j.end()) { // nothing to parse
        return -1;
      }

      json cals = j["calendars"];
      int numCals = cals.size();

      for (auto const& obj : cals) {
        int id = obj["id"];
        std::string name =  obj["name"];
        std::vector<int> fixedIds = obj["fixed"];
        std::vector<json> pauses = obj["pauses"]; // for latter use
        std::vector<json> offs = obj["offs"];
        std::vector<int> empty = {};
        start_off.insert(std::make_pair(id, empty));
        duration_off.insert(std::make_pair(id, empty));
        fixed_zero.insert(std::make_pair(id, fixedIds));

        for (auto const& off : offs) {
          int start = off["start"];
          int duration = off["duration"];
          start_off[id].push_back(start);
          duration_off[id].push_back(duration);
        }

        std::cout << id << " : " << name << " ; #fixed = " << fixedIds.size() << " ; #pauses = " << pauses.size() << " ; #offs = " << offs.size() << "\n";
      }
      return numCals;
    }

    int parseRooms(json j) {
      if (j.find("rooms") == j.end()) { // nothing to parse
        return -1;
      }

      json rooms = j["rooms"]; // {"id": 0, "name": "Crise 835G", "locationId": 0, "capacity": 12, "visio": false}
      int numRooms = rooms.size();

      for (auto const& obj : rooms) {
        int id = obj["id"];
        std::string name =  obj["name"];
        int locId = obj["locationId"];
        int cap = obj["capacity"];
        bool visio = obj["visio"];

        room_names.insert(std::make_pair(id, name));
        site_salle.insert(std::make_pair(id, locId));
        salles[locId].push_back(id);
        capacity.insert(std::make_pair(id, cap));
        if (!visio) {
          non_viso.push_back(id);
        }

        std::cout << id << " : " << name << " ; loc = " << locId << " ; cap = " << cap << " ; visio = " << visio << "\n";
      }
      return numRooms;
    }

    int parseDistances(json j) {
      if (j.find("distances") == j.end()) { // nothing to parse
        return -1;
      }

      json dists = j["distances"]; // {"id1": 0, "id2": 1, "time": 60},
      int numDists = dists.size();

      for (auto const& obj : dists) {
        int id1 = obj["id1"];
        int id2 = obj["id2"];
        int travelTime = obj["time"];
        travel.insert(std::make_pair(std::make_pair(id1, id2), travelTime));
        std::cout << "id1 = " << id1 << " ; id2 = " << id2 << " ; time = " << travelTime << "\n";
      }
      return numDists;
    }

  }; // end of class Data

  Model* wrapper;

  int tb(int id1, int id2) {
    if (id1 == id2) {
      return 0;
    }
    return wrapper->travel[std::make_pair(id1, id2)];
  }

  void Solve(std::istream& iStr, std::ostream& oStr) {
    Model model("Calendrier", 0, 10000);
    model.Load(iStr, oStr);
    wrapper = &model;
    model.createConstraints();
  }


} // end operations_research namespace

static const char kUsage[] =
"Usage: see flags.\nThis program runs something ";

int main(int argc, char** argv) {

  std::cout << __cplusplus << "\n";

  FLAGS_log_prefix = false;
  gflags::SetUsageMessage(kUsage);
  gflags::ParseCommandLineFlags(&argc, &argv, true);

  std::istream* iStr;
  std::ostream* oStr;


  if (FLAGS_input.empty()) {
    iStr = &std::cin;
  } else {
    LOG(INFO) << "Load " << FLAGS_input;
    std::ifstream ifStr(FLAGS_input, std::ifstream::in);
    iStr = &ifStr;
  }

  if (FLAGS_solution.empty()) {
    oStr = &std::cout;
  } else {
    LOG(INFO) << "Output " << FLAGS_solution;
    std::ofstream ofStr(FLAGS_solution, std::ofstream::app);
    oStr = &ofStr;
  }
  operations_research::Solve(*iStr, *oStr);

  return 0;
}
