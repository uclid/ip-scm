/*********************************************
 * OPL 12.8.0.0 Model
 * Author: Dixit
 * Creation Date: Dec 31, 2018 at 10:26:20 PM
 *********************************************/
tuple Elevator{
	key int id;
	int location;
	int lowest_floor; //lowest floor number that it can serve
	int highest_floor; //highest floor number that it can serve
}

tuple Request{
	key int id;
	int request_floor;
}

//a set of elevators
{Elevator} E = ...;

//request set, currently defined to contain 3 requests
{Request} R = ...;

//number of floors in the building
int floors = ...;

int numReqs = card(R);

//size of powerset except empty set
int setSize = ftoi(pow(2,numReqs))-1;
{Request} reqSets[i in 1..setSize]={};

//dummy prices and cost
int Cost[E][1..setSize];

dvar boolean select[E][1..setSize];

//Checked: this part correctly
//gives valid subsets (powerset 
//without the empty set) of 
//requests to be served by elevators
execute{
	for(var i in R){
  		for(var j = 1; j <= setSize ; j++){
			if ((j >> Opl.ord(R,i)) % 2 == 1) reqSets[j].add(i);
		}
	}
	writeln(reqSets);
}

//Calculate cost and price for each elevator 
//based on request subsets
execute {
	for(var i in E) {
		for(var j = 1; j <= setSize; j++){
			var minFloor = Opl.first(reqSets[j]);
			var maxFloor = Opl.last(reqSets[j]);
				
			var elevRange = maxFloor.request_floor - minFloor.request_floor;
			var distToClosest = Opl.minl(Opl.abs(i.location - minFloor.request_floor), Opl.abs(i.location - maxFloor.request_floor));
			
			var cost = elevRange + distToClosest;
			
			Cost[i][j] = cost;
		}
	}	

}

minimize
	sum(e in E) (sum (r in 1..setSize)(Cost[e][r]) * select[e][r]);
subject to {
	//2 Each elevator must serve exactly one request set to be in the sector coalition
	forall(e in E) (sum (r in 1..setSize) select[e][r]) == 1;
	
	//3 Only one elevator serves a request set
	forall(r in 1..setSize) (sum (e in E) select[e][r]) <= 1;
	
	//4 Total number of requests served should be consistent
	sum(e in E) (sum (r in 1..setSize) card(reqSets[r])*select[e][r]) == numReqs;
	
	//5 All individual requests must be served i.e. each request occurs just once in service
	forall(r1 in R) (sum(e in E) (sum (r in 1..setSize) (sum (r2 in reqSets[r]) (select[e][r]*(r1==r2))))) == 1;
	
	//6 The lowest floor of elevator sector must be the same or below the request floor
	forall(r in 1..setSize, e in E) (select[e][r]*e.lowest_floor) <= first(reqSets[r]).request_floor*select[e][r];
	
	//7 The highest floor of elevator sector must be the same or above the request floor
	forall(r in 1..setSize, e in E) (select[e][r]*e.highest_floor) >= last(reqSets[r]).request_floor*select[e][r];
	
}

tuple solutionT{
	int list;
};

int selected[r in 1..setSize] = ((sum(e in E) select[e][r] >= 1) ? 1:0);

{solutionT} list = { <r> | r in 1..setSize : selected[r] == 1 };

execute DISPLAY {
  	writeln("Selected=", list);
	for(var i in list){
		writeln(reqSets[i.list]);	
	}
}
