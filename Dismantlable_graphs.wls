#!/usr/bin/env wolframscript
(* ::Package:: *)

(*
Algorithm for determining cop-win graphs
By J\[EAcute]r\[EAcute]mie Turcotte

Uses the equivalence between cop-win and dismantlable graphs, see https://www.sciencedirect.com/science/article/pii/0012365X83901607.
*)


(* Returns the closed neighbourhood of v in g *)
closedNeighbourhood[g_,v_]:=Append[AdjacencyList[g,v],v]


(* Attemps to find a corner in the graph g *)
corner[g_]:=Module[{i,j},
	Catch[
		Do[
			If [i!=j,
				If[SubsetQ[closedNeighbourhood[g,i],closedNeighbourhood[g,j]],
					Throw[{True,j}] (* if the neighbourhood of j is a subset of the neighbourhood of i, then j is a corner/irreducible vertex *)
				]
			];
			,{i,VertexList[g]},{j,VertexList[g]}]; (* we test for all pairs of vertices (i,j), the if above makes sure that these are separate vertices *)
			Throw[{False,0}] (* if no corner is found *)
	]
]


(* Connected graphs up to order 3 are cop-win *)
copWin[g_]:=True/;VertexCount[g]<=3


(* Tests if the graph g (which we suppose is connected) is cop-win *)
copWin[g_]:=Module[{val=corner[g],containCorner,corner},

	containCorner=val[[1]];corner=val[[2]];

	If[containCorner,
		copWin[Subgraph[g,DeleteCases[VertexList[g],corner]]], (* if g contains a corner u, we remove it and verify if g-u is cop-win (note that if g is connected, so is g-u) *)
		False
	]
]


(* Example of how to import graph files*)
importData[i_]:=Flatten[{Import["/n10/graphs_10_1_10_"<>ToString[i]<>"_1000.g6","graph6"]}] (* the path is absolute *)


(* Example of code to manage reading each file and counting down the number of cop-win graphs *)
counter=0;

Do[
	tempList=importData[i];
	tempNumber=Count[Map[copWin,tempList],True];
	Print[ToString[i]<>" "<>ToString[tempNumber]];
	counter=counter+tempNumber;
	,{i,0,999}
]
	
Print[counter];
