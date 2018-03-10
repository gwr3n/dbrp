/*********************************************
* OPL 12.6.0.0 Model
* Author: Roberto Rossi
* Creation Date: Apr 12, 2016 at 4:02:27 PM
*********************************************/

execute{
	/* Set to 0 for no cuts */
	cplex.cutsfactor=1;
}

/* Assume node 1 is the location of the cistern */

int T = ...; // Time horizon
int M = ...; // Machines 
int N = ...; // Nodes in the site graph - node 1 is the cistern

range time = 1..T;
range nodes = 1..N;
range machines = 1..M;

/*Distance matrix*/
float distance[nodes][nodes] = ...;
/*Connectivity matrix*/
int connectivity [nodes][nodes] = ...;
/*Location of a machine at time t*/
int machineLocation[time][machines][nodes] = ...;
/*Machine fuel consumption*/
float fuelConsumption[machines][time] = ...; 
/*Machine initial tank level*/
float initialTankLevel[machines] = ...;
/*Machine tank capacity*/
float tankCapacity[machines] = ...;
/*Bowser capacity*/
float bowserCapacity = ...;
/*Initial bowser level*/
float initialBowserLevel = ...;
/*Initial bowser location*/
int initialBowserLocation = ...;
/*Machine stockout penalty cost*/
float penalty = ...;
/*Minimum order quantity for both Bowser and Machines*/
//int minOrderQty = 1;

/*Bowser location at time t*/
dvar int visit[nodes][time] in 0..1;
/*Bowser transition at time t*/
dvar int transit[1..T-1][nodes][nodes] in 0..1;
/*Quantity delivered to machine m at time t*/
dvar float+ qty[m in machines][time] in 0..tankCapacity[m];
//dvar int+ qtyUnits[machines][time];
/*Boswer refueling at time t*/
dvar float+ bowserRefuel[time] in 0..bowserCapacity;
//dvar int+ bowserRefuelUnits[time];
/*Machine fuel stockouts*/
dvar float+ stockout[machines][0..T];
dvar float+ stockouts;

/*Objective: minimize distance covered by the bowser*/
minimize sum(n1 in nodes, n2 in nodes, t in 2..T) transit[t-1][n1][n2]*distance[n1][n2] +
		 penalty*sum(t in time, m in machines) stockout[m][t];

subject to{
	/* Constraints enforcing a minumum order quantity for bowser and machines */
	//forall(m in machines, t in time) qty[m][t] == minOrderQty*qtyUnits[m][t];
	//forall(t in time) bowserRefuel[t] == minOrderQty*bowserRefuelUnits[t];

    stockouts == sum(m in machines, t in time) stockout[m][t];

	/*Bowser location at time 1*/
	visit[initialBowserLocation][1] == 1;
	
	/*Initial machine stockouts*/
	forall(m in machines) stockout[m][0] == maxl(-initialTankLevel[m],0);
	
	/*Channeling constraint between visit and transit*/
	forall(n1 in nodes, n2 in nodes, t in 2..T){ 
		transit[t-1][n1][n2]>=visit[n1][t-1]+visit[n2][t]-1;
		transit[t-1][n1][n2]<=visit[n1][t-1];
		transit[t-1][n1][n2]<=visit[n2][t];
    }		
	
	/*Bowser cannot be refuelled unless at cistern*/
	forall(t in time) bowserRefuel[t] <= bowserCapacity*visit[1][t]; 
	/*Bowser capacity constraints*/	
	forall(t in 1..T) 
		initialBowserLevel + 
		sum(tt in 1..t) bowserRefuel[tt] - 
		sum(tt in 1..t-1) sum(m in 1..M) qty[m][tt] <= bowserCapacity;
	/*Bowser refueling and inventory conservation constraints*/	
	forall(t in 1..T) 
		initialBowserLevel + 
		sum(tt in 1..t) bowserRefuel[tt] - 
		sum(tt in 1..t) sum(m in 1..M) qty[m][tt] >= 0;
	
	/*At each point in time bowser must be somewhere*/
	forall(t in time) sum(n in nodes) visit[n][t] == 1;
	/*Bowser can transit to node n2 only if n1 and n2 are connected*/
	forall(n1 in nodes, t in 2..T)  sum(n2 in nodes) transit[t-1][n1][n2]*connectivity[n1][n2] == visit[n1][t-1];
	/*If bowser is in n1 at time t, it must transit somewhere*/
	forall(n1 in nodes, t in 2..T)  sum(n2 in nodes) transit[t-1][n1][n2] == visit[n1][t-1];

	/*Machine refueling and inventory conservation constraints*/	
	forall(t in time, m in machines) 
		initialTankLevel[m] + 
		sum(tt in 1..t) qty[m][tt] +
		sum(tt in 0..t-1) stockout[m][tt] - 
		sum(tt in 1..t) fuelConsumption[m][tt]
		>= -stockout[m][t];
	forall(t in time, m in machines) 
		initialTankLevel[m] + 
		sum(tt in 1..t) qty[m][tt] +
		sum(tt in 0..t-1) stockout[m][tt] - 
		sum(tt in 1..t-1) fuelConsumption[m][tt]
		<= tankCapacity[m];
		
	forall(t in time, m in machines)
		stockout[m][t] <= fuelConsumption[m][t];

	/*Machine can be refuelled only if both machine and boswer are at node n*/
	forall(m in machines, t in time) qty[m][t] <= tankCapacity[m]*sum(n in nodes)(visit[n][t]*machineLocation[t,m,n]);
}