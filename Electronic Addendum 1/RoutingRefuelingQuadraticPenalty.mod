/*********************************************
* OPL 12.6.0.0 Model
* Author: Roberto Rossi
* Creation Date: Apr 12, 2016 at 4:02:27 PM
*********************************************/
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
int fuelConsumption[machines][time] = ...; 
/*Machine initial tank level*/
float initialTankLevel[machines] = ...;
/*Machine tank capacity*/
float tankCapacity[machines] = ...;
/*Bowser capacity*/
float bowserCapacity = ...;
/*Initial bowser level*/
float initialBowserLevel = ...;
/*Machine stockout penalty cost*/
float penalty = 50;

/*Cumulative demand*/
float cumulativeDemand = sum(m in machines, t in time) fuelConsumption[m][t];
float excess[m in machines] = maxl(0, initialTankLevel[m] - sum(t in time) fuelConsumption[m][t]);

/*Bowser location at time t*/
dvar int visit[nodes][time] in 0..1;
/*Quantity delivered to machine m at time t*/
dvar float+ qty[m in machines][time] in 0..tankCapacity[m];
/*Boswer refueling at time t*/
dvar float+ bowserRefuel[time] in 0..bowserCapacity;
/*Machine fuel stockouts*/
dvar float+ stockout[machines][0..T];

/*Objective: minimize distance covered by the bowser*/
minimize sum(n1 in nodes, n2 in nodes, t in 2..T) visit[n1][t-1]*visit[n2][t]*distance[n1][n2] +
		 penalty*sum(t in time, m in machines) stockout[m][t];

subject to{
	/*Bowser is at the cistern location at time 1*/
	visit[1][1] == 1;
	
	forall(m in machines) stockout[m][0] == 0;
	
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
	/*Bowser cuts*/
	sum(tt in 1..T) bowserRefuel[tt] <= maxl(0, cumulativeDemand - 
												sum(tt in 1..T) sum(m in machines) stockout[m][tt] - 
												sum(m in machines)initialTankLevel[m] - 
												initialBowserLevel + 
												sum(m in machines)excess[m]);
	sum(tt in 1..T) sum(m in 1..M) qty[m][tt] <= initialBowserLevel + sum(tt in 1..T) bowserRefuel[tt];
	
	/*At each point in time bowser must be somewhere*/
	forall(t in time) sum(n in nodes) visit[n][t] == 1;
	/*Bowser can transit to node n2 only if n1 and n2 are connected*/
	forall(n1 in nodes, n2 in nodes, t in 2..T) connectivity[n1][n2] >= visit[n1][t-1] + visit[n2][t] - 1;

	/*Machine refueling and inventory conservation constraints*/
	forall(t in time, m in machines) 
		minl(
		initialTankLevel[m] + 
		sum(tt in 1..t) qty[m][tt] +
		sum(tt in 0..t-1) stockout[m][tt] - 
		sum(tt in 1..t) fuelConsumption[m][tt], 0) <= -stockout[m][t];
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
	
	/*Machine can be refuelled only if both machine and boswer are at node n*/
	forall(m in machines, t in time) qty[m][t] <= tankCapacity[m]*sum(n in nodes)(visit[n][t]*machineLocation[t,m,n]);
	/*Refueling quantity should be less than future consumption minus tank level at time t*/
	forall(m in machines, n in nodes, t in time) qty[m][t] <= 
		maxl(0, sum(tt in t..T) (fuelConsumption[m][tt] - stockout[m][tt]) - 
				(initialTankLevel[m] + sum(tt in 1..t-1) (qty[m][tt] + stockout[m][tt-1] - fuelConsumption[m][tt])));
	
	
	/*Safety constraints*/
	//forbidden to remain stationary at any node except node 1
	forall(n in 2..N, t in 2..T) visit[n][t-1] + visit[n][t] <= 1;
}