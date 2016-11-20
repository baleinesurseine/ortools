#include <cstdio>
#include <fstream>
#include <iostream>
#include "constraint_solver/constraint_solver.h"
#include "util/json.hpp"

// Want to say Hello ? contact <base64>ZWRvdWFyZC5maWNoZXJAZ21haWwuY29t

// for convenience
using json = nlohmann::json;

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
      for (auto const& taskDur : opt_dur) {
        int taskId = taskDur.first;
        int duration = taskDur.second;
        IntVar* dr = solv.MakeIntVar(min_t, max_t);
        d.insert(std::make_pair(taskId, dr));
        IntervalVar* sr = solv.MakeFixedDurationIntervalVar(dr, duration, task_names[taskId]);
        s.insert(std::make_pair(taskId, sr));
      }
      // 0.b - Create fixed meetings
      for (auto const& taskDur : fixed_dur) {
        int taskId = taskDur.first;
        int duration = taskDur.second;
        int start = fixed_start[taskId];
        IntervalVar* sr = solv.MakeFixedInterval(start, duration, task_names[taskId]);
        s.insert(std::make_pair(taskId, sr));
      }

      // 1 - Début de la réunion après la date au plus tôt
      for (auto const& after : opt_after) {
        int taskId= after.first;
        int dateAfter = after.second;
        IntExpr* delr = solv.MakeDifference(dateAfter, d[taskId]);
        solv.MakeLessOrEqual(delr, 0); // CHECK if correct direction of comparison
      }

      // 2 - Calcul du nombre de personnes par site pour une réunion
      // 2.a - Initialisation de e_r,l
      int nb_pers = people_names.size(); // count number of persons
      for (auto const& taskInterval : s) { // loop on all tasks
        int taskId = taskInterval.first;
        for (auto const& locationName : location_names) { // loop on all locations
          int locationId = locationName.first;
          IntVar* erl = solv.MakeIntVar(0, nb_pers);
          e.insert(std::make_pair(std::make_pair(taskId, locationId), erl));
        }
      }
      // 2.b - Initialisation de l_p,r
      std::vector<int> all_loc; // list of all locations
      for (auto const& locationName : location_names) {
        int locationId = locationName.first;
        all_loc.push_back(locationId);
      }
      for (auto const& taskInterval : s) { // loop on all tasks
        int taskId = taskInterval.first;
        std::vector<int> parts = participants[taskId];
        if (opt_dur.find(taskId) != opt_dur.end()) { // optimized task
          for (auto const& part : parts) {
            IntVar* lpr = solv.MakeIntVar(all_loc); // initial domain is all locations
            l.insert(std::make_pair(std::make_pair(part, taskId), lpr));
          }
        } else { // fixed task
          int loc = fixed_loc[taskId];
          for (auto const& part : parts) {
            IntVar* lpr = solv.MakeIntVar(loc, loc); // initial domain is singleton
            l.insert(std::make_pair(std::make_pair(part, taskId), lpr));
          }
        }
      }
      // 2.c - Calcul
      for (auto const& taskInterval : s) { // loop on all tasks
        int taskId = taskInterval.first;
        std::vector<int> parts = participants[taskId]; // participants of task
        std::vector<IntVar*> lprs; // list of participants to task
        for (auto const& part : parts) {
          IntVar* lpr = l[std::make_pair(part, taskId)];
          lprs.push_back(lpr);
        }
        for (auto const& locationName : location_names) { // loop on all locations
          int locationId = locationName.first;
          solv.MakeCount(lprs, locationId, e[std::make_pair(taskId, locationId)]);
        }
      }

      // 3 - Au plus une salle par site pour une même réunion
      // 3.a - Init booleans a_s,r
      for (auto const& roomName : room_names) {
        int roomId = roomName.first;
        for (auto const& taskInterval : s) {
          int taskId = taskInterval.first;
          IntVar* asr = solv.MakeBoolVar();
          a.insert(std::make_pair(std::make_pair(roomId, taskId),asr));
        }
      }
      // 3.b - Add constraints
      // 4 - Capacité de la salle de réunion
      for (auto const& taskInterval : s) {
        int taskId = taskInterval.first;
        for (auto const& locationName : location_names) {
          int locationId = locationName.first;
          std::vector<IntVar*> asrl;
          std::vector<int> caprl;
          std::vector<int> sl = salles[locationId];
          for (auto const& salle : sl) {
            asrl.push_back(a[std::make_pair(salle, taskId)]);
            caprl.push_back(capacity[salle]);
          }
          solv.MakeSumLessOrEqual(asrl, 1);
          asrl.push_back(e[std::make_pair(taskId, locationId)]);
          caprl.push_back(-1);
          solv.MakeScalProdGreaterOrEqual(asrl, caprl, 0);
        }
      }

      // 5 - Au plus une réunion par salle à tout instant
      for (auto const& roomName : room_names) {
        int salleId = roomName.first;
        std::vector<IntVar*> asr;
        std::vector<IntervalVar*> sr;
        for (auto const& taskInterval : s) {
          int taskId = taskInterval.first;
          asr.push_back(a[std::make_pair(salleId, taskId)]);
          sr.push_back(s[taskId]);
        }
        solv.MakeCumulative(sr, asr, 1, "capacité salle");
      }

      // 6 - Détection du multisite de chaque réunion
      std::vector<int> locationIds = {};
      for (auto const& location : location_names) {
        locationIds.push_back(location.first);
      }

      for (auto const& taskInterval : s) {
        int taskId = taskInterval.first;
        IntVar* lb = solv.MakeIntVar(locationIds);
        IntVar* ub = solv.MakeIntVar(locationIds);
        IntVar* mr = solv.MakeBoolVar();
        m.insert(std::make_pair(taskId, mr));
        std::vector<IntVar*> lpr;
        for (auto const& peopleId : participants[taskId]) {
          lpr.push_back(l[std::make_pair(peopleId, taskId)]);
        }
        solv.MakeMinEquality(lpr, lb);
        solv.MakeMaxEquality(lpr, ub);
        solv.MakeIsDifferentCt(lb, ub, mr);
      }

      // 7 - Visio dans chaque salle si multisite
      for (auto const& taskInterval : s) {
        int taskId = taskInterval.first;
        std::vector<IntVar*> asr; // non-visio rooms used for task
        for (auto const& roomId : non_viso) {
          asr.push_back(a[std::make_pair(roomId, taskId)]);
        }
        solv.MakeEquality(solv.MakeProd(m[taskId],solv.MakeSum(asr)), 0);
      }
      // 8 - Temps de trajet
      for (auto const& peopleName : people_names) { // loop on people
        int peopleId = peopleName.first;
        std::vector<int> tasks = meetings[peopleId];
        std::vector<IntVar*> dr; // starting times of people's tasks
        std::vector<int> tr; // durations of people's tasks
        std::vector<IntVar*> lr; // locationIds of people's tasks
        std::vector<IntVar*> dspq; // sorted starting times of people's tasks

        int q = 0;
        for (auto const& taskId : tasks) {
          dr.push_back(d[taskId]);
          tr.push_back(durations[taskId]);
          lr.push_back(l[std::make_pair(peopleId, taskId)]);
          IntVar* ds_pq = solv.MakeIntVar(min_t, max_t);
          ds.insert(std::make_pair(std::make_pair(peopleId, q), ds_pq));
          dspq.push_back(ds_pq);
          q += 1;
        }

        int nbq = q;
        cout << "People: " << peopleName.second << " ; q: " << nbq << "\n";
        solv.MakeSortingConstraint(dr, dspq); // ds_pq est l'heure de début de la q_ième réunion de p

        for (q = 0; q < nbq; q++) {
          IntVar* i_pq = solv.MakeIntVar(tasks);
          IntVar* ds_pq = ds[std::make_pair(peopleId, q)];

          solv.MakeElementEquality(dr, i_pq, ds_pq);
          IntExpr* f_pq = solv.MakeSum(ds_pq, solv.MakeElement(tr, i_pq));
          f.insert(std::make_pair(std::make_pair(peopleId, q), f_pq));
          IntExpr* ls_pq = solv.MakeElement(lr, i_pq);
          ls.insert(std::make_pair(std::make_pair(peopleId, q), ls_pq));
        }

        for (q=0; q < nbq - 1; q++) {
          IntVar* ls_pq = ls[std::make_pair(peopleId, q)]->Var();
          IntVar* ls_pqp = ls[std::make_pair(peopleId, q+1)]->Var();
          IntExpr* tr_pq = solv.MakeElement(tb, ls_pq, ls_pqp);
          IntExpr* f_pq = f[std::make_pair(peopleId, q)];
          IntExpr* z_pq = solv.MakeSum(f_pq, tr_pq);
          z.insert(std::make_pair(std::make_pair(peopleId, q), z_pq));
          solv.MakeLessOrEqual(z_pq, ds[std::make_pair(peopleId, q+1)]);
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
      oStr << parseZeroTasks() << " task(s)\n";
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
    std::map<int, int> workPlaces;


    int parseLocations(json j) {
      if (j.find("locations") == j.end()) { // nothing to parse
        return -1;
      }

      json locations = j["locations"];
      int numLocs = locations.size();

      for (auto const& location : locations) {
        int locationId = location["id"];
        std::string name =  location["name"];
        location_names.insert(std::make_pair(locationId, name));
        std::vector<int> empty = {};
        salles.insert(std::make_pair(locationId, empty));
        std::cout << locationId << " : " << name << "\n";
      }
      return numLocs;
    }

    int parsePeople(json j) {
      if (j.find("people") == j.end()) { // nothing to parse
        return -1;
      }
      json peoples = j["people"]; //   {"id": 0, "name": "Edouard Fischer", "workplaceId": 0, "calendars": [42]}
      int numPeople = peoples.size();

      for (auto const& people : peoples) {
        int peopleId = people["id"];
        std::vector<int> un_part = {peopleId};
        std::string name =  people["name"];
        int workplaceId = people["workplaceId"];
        workPlaces.insert(std::make_pair(peopleId, workplaceId));
        std::vector<int> calendarIds = people["calendars"];
        std::vector<int> empty1 = {};
        people_names.insert(std::make_pair(peopleId, name));
        meetings.insert(std::make_pair(peopleId, empty1));
        std::vector<int> empty2 = {};
        solo.insert(std::make_pair(peopleId, empty2));
        off_calendars.insert(std::make_pair(peopleId, calendarIds));

        std::cout << peopleId << " : " << name << " ; wp = " << workplaceId << " ; #cals = " << calendarIds.size() << "\n";
      }
      return numPeople;
    };

    int parseZeroTasks() {
      int zero_task_id = (--task_names.end())->first + 1;
      for (auto const& people : people_names) {
        int peopleId = people.first;
        std::vector<int> un_part = {peopleId};
        std::vector<int> calendarIds = off_calendars[peopleId];
        int workplaceId = workPlaces[peopleId];

        //int zero_task_id = 10000;
        for (auto const& calendarId : calendarIds) {
          std::vector<int> fixedIds = fixed_zero[calendarId];
          for (auto const& zero_start : fixedIds) {
            fixed_start.insert(std::make_pair(zero_task_id, zero_start));
            fixed_dur.insert(std::make_pair(zero_task_id, 0));
            durations.insert(std::make_pair(zero_task_id, 0));
            fixed_room.insert(std::make_pair(zero_task_id, workplaceId));
            fixed_loc.insert(std::make_pair(zero_task_id, site_salle[workplaceId]));
            participants.insert(std::make_pair(zero_task_id, un_part));
            meetings[peopleId].push_back(zero_task_id);
            solo[peopleId].push_back(zero_task_id);
            zero_task_id++;
          }
        }
      }
      return zero_task_id;
    }

    int parseTasks(json j) {
      if (j.find("locations") == j.end()) { // nothing to parse
        return -1;
      }

      json tasks = j["tasks"];
      int numTasks = tasks.size();

      for (auto const& task : tasks) {
        int taskId = task["id"];
        std::string name =  task["name"];
        std::vector<int> memberIds = task["members"];
        int duration = task["duration"];

        task_names.insert(std::make_pair(taskId, name));
        participants.insert(std::make_pair(taskId, memberIds));
        for (auto const& peopleId : memberIds) {
          meetings[peopleId].push_back(taskId);
        }
        if (memberIds.size() == 1) {
          solo[memberIds[0]].push_back(taskId);
        }

        int start = -1;
        int locationId = -1;
        int roomId = -1;
        int after = -1;
        if (task.find("start") == task.end()) // réunion à optimiser
        {
          opt_dur.insert(std::make_pair(taskId, duration));
          durations.insert(std::make_pair(taskId, duration));
          after = task["after"];
          opt_after.insert(std::make_pair(taskId, after));
        } else { // réunion fixée
          start = task["start"];
          locationId = task["location"];
          roomId = task["room"];
          fixed_start.insert(std::make_pair(taskId, start));
          fixed_dur.insert(std::make_pair(taskId, duration));
          durations.insert(std::make_pair(taskId, duration));
          fixed_loc.insert(std::make_pair(taskId, locationId));
          fixed_room.insert(std::make_pair(taskId, roomId));
        }

        std::cout << taskId << " : " << name << " ; loc = " << locationId << " ; duration = " << duration << " ; #members = " << memberIds.size() << "\n";
      }
      return numTasks;
    }

    int parseCalendars(json j) {
      if (j.find("calendars") == j.end()) { // nothing to parse
        return -1;
      }

      json cals = j["calendars"];
      int numCals = cals.size();

      for (auto const& calendar : cals) {
        int calendarId = calendar["id"];
        std::string name =  calendar["name"];
        std::vector<int> fixedIds = calendar["fixed"];
        std::vector<json> pauses = calendar["pauses"]; // for latter use
        std::vector<json> offs = calendar["offs"];
        std::vector<int> empty1 = {};
        start_off.insert(std::make_pair(calendarId, empty1));
        std::vector<int> empty2 = {};
        duration_off.insert(std::make_pair(calendarId, empty2));
        fixed_zero.insert(std::make_pair(calendarId, fixedIds));

        for (auto const& off : offs) {
          int start = off["start"];
          int duration = off["duration"];
          start_off[calendarId].push_back(start);
          duration_off[calendarId].push_back(duration);
        }

        std::cout << calendarId << " : " << name << " ; #fixed = " << fixedIds.size() << " ; #pauses = " << pauses.size() << " ; #offs = " << offs.size() << "\n";
      }
      return numCals;
    }

    int parseRooms(json j) {
      if (j.find("rooms") == j.end()) { // nothing to parse
        return -1;
      }

      json rooms = j["rooms"]; // {"id": 0, "name": "Crise 835G", "locationId": 0, "capacity": 12, "visio": false}
      int numRooms = rooms.size();

      for (auto const& room : rooms) {
        int roomId = room["id"];
        std::string name =  room["name"];
        int locationId = room["locationId"];
        int cap= room["capacity"];
        bool visio = room["visio"];

        room_names.insert(std::make_pair(roomId, name));
        site_salle.insert(std::make_pair(roomId, locationId));
        salles[locationId].push_back(roomId);
        capacity.insert(std::make_pair(roomId, cap));
        if (!visio) {
          non_viso.push_back(roomId);
        }

        std::cout << roomId << " : " << name << " ; loc = " << locationId << " ; cap = " << cap << " ; visio = " << visio << "\n";
      }
      return numRooms;
    }

    int parseDistances(json j) {
      if (j.find("distances") == j.end()) { // nothing to parse
        return -1;
      }

      json dists = j["distances"]; // {"id1": 0, "id2": 1, "time": 60},
      int numDists = dists.size();

      for (auto const& dist : dists) {
        int id1 = dist["id1"];
        int id2 = dist["id2"];
        int travelTime = dist["time"];
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
    Model model("Calendrier", 61420800, 61431000);
    model.Load(iStr, oStr);
    wrapper = &model;
    model.createConstraints();
  }
} // end operations_research namespace

int main(int argc, char** argv) {
  operations_research::Solve(std::cin, std::cout);
  return 0;
}
