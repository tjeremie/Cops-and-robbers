(* ::Package:: *)

(* 
	Generating small 4-cop-win candidate graphs - Part 1
	
	For Finding the minimum order of 4-cop-win graphs
	By J\[EAcute]r\[EAcute]mie Turcotte and Samuel Yvon
*)


(* Usage
	Running this file takes a few hours but will generate all the results required for part 2 of the algorithm, for every case we need to prove the proposition.
*)


(* CODE *)


(* Debugging function to print a graph with labels *)
printLabel[g_]:=Graph[g,VertexLabels->"Name"]


(* Some functions on neighbourhoods *)
openNeighbourhood[g_,v_]:=AdjacencyList[g,v] (* The neighbourhood of v in g. *)
closedNeighbourhood[g_,v_]:=Prepend[AdjacencyList[g,v],v] (* The closed neighbourhood (includes v) of v in g. *)
noNeighbourhood[g_,v_]:=Complement[VertexList[g],closedNeighbourhood[g,v]] (* The set of vertices of g-N[v]. *)


(* Functions to create formal edges *)
convertToEdge[v_,list_]:=(v\[UndirectedEdge]#)&/@list (* Returns a list of edges between v and the vertices of list. *)
doubleConvertToEdge[v1_,v2_,list_]:=Join[convertToEdge[v1,list],convertToEdge[v2,list]] (* Returns a list of edges between the vertices in list and v1 and with v2. *)


(* Functions to reduce vertices to consider by automorphism *)
automorphismsImage[automorphismList_,v_]:=Union[Map[#[v]&,automorphismList]] (* Given a list of automorphisms (encoded as associations) of some graph, returns all vertices equivalent to v through one of these automorphisms. *)
automorphicEquivalentVertices[g_,v_]:=automorphismsImage[FindGraphIsomorphism[g,g,All],v] (* Given a graph g and a vertex v, returns all vertices equivalent to v through some automorphism of g. *)
reduceByAutomorphism[g_,list_]:=DeleteDuplicates[list,MemberQ[automorphicEquivalentVertices[g,#1],#2]&] (* Given a graph g and a list of vertices of g, removes from this list vertices which are equivalent through some automorphism. *)


(* Functions relating to the maximum authorized possible degree of vertices *)
realDegreeBound[v_,lowerDegreeVerticesList_, maxDeg_]:=maxDeg-Boole[MemberQ[lowerDegreeVerticesList,v]] (* Given maxDeg, which is the maximum authorized degree we consider, and a list of vertices whose degree must be strictly smaller than maxDeg, returns the maximum possible degree of v (either maxDeg or maxDeg-1). *)
degreesFilter[g_,lowerDegreeVerticesList_,maxDeg_]:=If[AllTrue[VertexList[g],VertexDegree[g,#]<=realDegreeBound[#,lowerDegreeVerticesList,maxDeg] &],g,Nothing] (* Verifies if the maximum degree of g is at most maxDeg and all vertices in lowerDegreeVerticesList have strictly smaller degree. If true, returns g, otherwise returns Nothing (an element which vanishes in any list). *)


(* Functions to reduce graphs to consider by isomorphism *)
fixedPointsIsomorphism[iso_,list_]:=AllTrue[list,Sort[#/.iso]==Sort[#]&] (* Given an isomorphism iso (encoded as an association) between two graphs on the same set vertices and a list of sets of vertices, returns true if the image (through iso) of every such set of vertices is itself. *)
strongIsomGraphs[g1_,g2_,list_]:=AnyTrue[FindGraphIsomorphism[g1,g2,All],fixedPointsIsomorphism[#,list]&] (* Given two graphs and a list of sets of vertices, returns true if there exists an isomorphism between g1 and g2 such that the image of every set of vertices is itself (which is what we call a "strong isomorphism"). *)


(* Functions used in the labelling of new vertices *)
verticesToAdd[g2_,v2_,maxDeg_,nbInteriorVertices_]:=nbInteriorVertices+Range[maxDeg-VertexDegree[g2,v2]] (* The list of vertices that will need to be added as common neighbors of v1 and v2 when merging the graphs. *)
alreadyNeighbours[g2_,v2_,maxDeg_,nbTotalVertices_]:=nbTotalVertices-Range[VertexDegree[g2,v2]] (* The list of labels we will give to the current neighbours of v2 when merging the graphs. *)
graphSections[g1_,v1_,g2_,v2_,maxDeg_,nbTotalVertices_]:={{v1},openNeighbourhood[g1,v1],noNeighbourhood[g1,v1],verticesToAdd[g2,v2,maxDeg,VertexCount[g1]],alreadyNeighbours[g2,v2,maxDeg,nbTotalVertices],{nbTotalVertices}} (* The six classes of vertices in the merged graph g, as described in the proof. *)


(* Functions to merge graphs g1 and g2 relative to a choice of v1 and v2 *)
removeIsoAndClean[list_,g1_,v1_,g2_,v2_,lowerDegreeVerticesList_,maxDeg_,nbTotalVertices_]:=DeleteDuplicates[degreesFilter[#,lowerDegreeVerticesList,maxDeg]&/@list,strongIsomGraphs[#1,#2,graphSections[g1,v1,g2,v2,maxDeg,nbTotalVertices]]&] (* Deletes in list the graphs not respecting the authorized degrees and removes graphs which are strongly isomorphic. It is important to note that it would technically also be necessary to verify that this isomorphism is compatible with the list of degrees which must have degree strictly smaller than maxDeg. But as we use our strong isomorphisms to, in particular, fix g1, the restriction of the isomorphism will also be an automorphism of g1, and as equivalent vertices have the same degree bounds, this is valid. *)
subgraphIsomorphisms[g1_,v1_,g2_,v2_]:=FindGraphIsomorphism[Subgraph[g2,noNeighbourhood[g2,v2]],Subgraph[g1,noNeighbourhood[g1,v1]],All]  (* Lists all isomorphisms (encoded as associations) from g2-N[v2] to g1-N[v1]. *)
mergeGraphsWithSpecificIso[g1_,v1_,g2_Graph,v2_,iso_,maxDeg_,nbTotalVertices_]:=EdgeAdd[GraphUnion[g1,VertexReplace[g2,Join[Normal[iso],Table[closedNeighbourhood[g2,v2][[i]]->nbTotalVertices-i+1,{i,VertexDegree[g2,v2]+1}]]]],doubleConvertToEdge[v1,nbTotalVertices,verticesToAdd[g2,v2,maxDeg,VertexCount[g1]]]] (* Merge graphs g1 and g2 with the following rules. Keep the numbering of g1, relabel v2 and it's neighbourhood respectively with labels nbVertices and nbVertices-1 to nbVertices-d_g2(v2). Relabel g2-N[v2] using the isomorphism iso (which is an isomorphism between g2-N[v2] and g1-N[v1]) to be able to merge with g1. If d_g1(v1)<maxDeg, add common neighbors to v1 and v2 to bring v2 to maximum degree. *)
mergeGraphs[g1_,v1_,g2_,v2_,lowerDegreeVerticesList_,i_,maxDeg_,nbTotalVertices_]:={#,graphSections[g1,v1,g2,v2,maxDeg,nbTotalVertices],lowerDegreeVerticesList,i}&/@removeIsoAndClean[mergeGraphsWithSpecificIso[g1,v1,g2,v2,#,maxDeg,nbTotalVertices]&/@subgraphIsomorphisms[g1,v1,g2,v2],g1,v1,g2,v2,lowerDegreeVerticesList,maxDeg,nbTotalVertices] (* Merge graphs g1 and g2 as above, by considering every possible way of merging g1-N[v1] and g2-N[v2]. Also adds to every graph relevant information for the next part of the algorithm (which is adding possible missing edges). *)


(* Functions to choose vertices depending on degree *)
selectDegreeVertices[g_,deg_]:=Select[VertexList[g],VertexDegree[g,#]==deg&] (* Returns all vertices of degree deg in g. *)
selectUpperDegreeVertices[g_,deg_]:=Select[VertexList[g],VertexDegree[g,#]>deg&] (* Returns all vertices of degree greater than deg in g.*)


(* Function to clean the list of graphs we are going to merge *)
cleanGraphList[list_,lower_,upper_]:=Sort[CanonicalGraph/@Select[list,Min[VertexDegree[#]]<=lower&&Max[VertexDegree[#]]<=upper&],Max[VertexDegree[#1]]>=Max[VertexDegree[#2]]&] (* Returns a cleaned version of list: sorts the graphs by decreasing maximum degree and only keeps graphs such that the maximum degree is at most upper and the minimum degree is at most lower. *)


(* Main function *

	Parameters
		nbTotalVertices: The total number of vertices in the graphs we will create.
		v1degree: The degree of the vertices v1 we will choose in g1.
		g1MaximumDegree: The maximum degree of the graphs g1 we will choose.
		maxDeg: The maximum degree of the graphs we will create.
		testAll: If True, graphs will be created for each possible choice of v1 in g1, otherwise will be done for one choice of v1.
		v2DegreeSmall: If True, will set the degree of v2 to be v1Degree+1. This mode will suppose that g-N[v1] has maximum degree 4. Only works on 18 vertices with maximum degree 5. Otherwise, v1 and v2 always will have the same degree, both in g1, g2 and in the resulting graphs.


	Output
		Exports to file a list whose first element is the list of graphs in which we will choose g1 and in which the second element is a list where each item is itself a list of length 4:
			The first item is the created graph.
			The second item is the breakdown into the 6 types of vertices of the graph.
			The third item is the list of vertices which must have maximum degree strictly smaller than maxDeg, this is useful to reduce the number of cases in part 2 of the algorithm.
			The fourth item is the position of g1 in the list of graphs that will be loaded, this will also be used to reduced the number of cases in part 2 of the algorithm.

	Note
		For simplicity of usage, this function requires internet access to fetch the required lists of 3-cop-win graphs. One could also download the files and read them directly.
*)



createGraphs[nbTotalVertices_,v1degree_,g1MaximumDegree_,maxDeg_,testAll_,v2DegreeSmaller_]:=
Block[{graphList1,graphList2,start,end,g1,v1,lowerDegreeVerticesList,reducedVerticesToConsider,results,v2degree},
	(* We load the proper list of graphs depending on the parameters. *)
	graphList1=cleanGraphList[Import["https://www.jeremieturcotte.com/research/4copsdata/smallgraphs/results/3copwingraphs/n"<>ToString[nbTotalVertices-maxDeg-1]<>"d1D"<>ToString[If[maxDeg==4 && nbTotalVertices-maxDeg-1==12,5,maxDeg]]<>"_3cops.g6","graph6"],maxDeg-1,maxDeg];  (*The list of connected graphs on nbInteriorVertices vertices such that c(G)=3 with Delta\[LessEqual]maxDeg, we also remove regular graphs*)
	
	v2degree=v1degree+Boole[v2DegreeSmaller]; (* In general, v1 and v2 will both have same degree both in g1,g2 and in the resulting graphs. In the special mode, we choose v2 to have degree 1 more than v1. *)
	
	graphList2=If[v2DegreeSmaller,Import["https://www.jeremieturcotte.com/research/4copsdata/smallgraphs/results/3copwingraphs/n13d1D4_3cops.g6","graph6"],graphList1];
	
	(* We select the start and the end indices of all graphs with maximum degree exactly g1MaximumDegree in graphList. *)
	start=FirstPosition[graphList1,_?(Max[VertexDegree[#]]==g1MaximumDegree&)][[1]];
	end=Length[graphList1]+1-FirstPosition[Reverse[graphList1],_?(Max[VertexDegree[#]]==g1MaximumDegree&)][[1]];
	
	results=AbsoluteTiming[Flatten[
		Table[
			(* For each possible graph g1 with maximum degree exactly g1MaximumDegree, we will also reduce by automorphism the possible choices of v1. *)
			g1=graphList1[[i]];
			reducedVerticesToConsider=reduceByAutomorphism[g1,selectDegreeVertices[g1,v1degree]];
			
			Table[
				(* We choose a vertex v1. *)
				v1=reducedVerticesToConsider[[j]];
				
				(* All vertices which either come before v1 in reducedVerticesToConsider or which have higher degree than v1 are considered to already having been considered. *)
				lowerDegreeVerticesList=If[v2DegreeSmaller,Range[12],Union[Flatten[Table[automorphicEquivalentVertices[g1,reducedVerticesToConsider[[k]]],{k,1,j-1}]],selectUpperDegreeVertices[g1,v1degree]]];
				
				(* For some choice of g2,v2, we compute the merged list. *)
				mergeGraphs[g1,v1,g2,v2,lowerDegreeVerticesList,i,maxDeg,nbTotalVertices]
	
				,{j,1,If[testAll,Length[reducedVerticesToConsider],Boole[Length[reducedVerticesToConsider]>0]]},{g2,graphList2[[If[v2DegreeSmaller,1,i];;Length[graphList2]]]},{v2,reduceByAutomorphism[g2,selectDegreeVertices[g2,v2degree]]} (* We only need to consider the graphs g2 which come after g1 in the list, and we consider v2 of the same degree as v1, but here again we can reduced the cases by automorphisms. *)
			]	
			,{i,start,end}
		]
		,4 (* We flatten 4 layers as there are 4 levels in our table. *)
	]];
	
	Print["List length: "<>ToString[Length[results[[2]]]]];
	Print["Computation time: "<>ToString[results[[1]]]];
	
	Export["/Users/jeremieturcotte/Desktop/"<>"basegraphs_"<>ToString[nbTotalVertices]<>"_"<>ToString[v1degree]<>"_"<>ToString[g1MaximumDegree]<>"_"<>ToString[maxDeg]<>"_"<>ToString[testAll]<>"_"<>ToString[v2DegreeSmaller]<>".mx",{graphList1,results[[2]]}]
]


(* RESULTS *)


(* Cases with v1 and v2 of same degree *)


(* Cases for n=18, Delta=5 *)


(* Choose g1 with maximum degree 5, v1 of degree 5 *)
createGraphs[18,5,5,5,False,False];

(* Sample results
	List length: 7426
	Computation time: 153.768
*)


(* Choose g1 with maximum degree 4, v1 of degree 4 in g1 *)
createGraphs[18,4,4,5,True,False];

(* Sample results
	List length: 3335
	Computation time: 139.402
*)


(* Choose g1 with maximum degree 4, v1 of degree 3 in g1 *)
createGraphs[18,3,4,5,True,False];

(* Sample results
	List length: 134
	Computation time: 213.353
*)


(* Choose g1 with maximum degree 4, v1 of degree 2 in g1 *)
createGraphs[18,2,4,5,True,False];

(* Sample results
	List length: 45
	Computation time: 4.2331
*)


(* Choose g1 with maximum degree 4, v1 of degree 1 in g1 *)
createGraphs[18,1,4,5,True,False];

(* Sample results
	List length: 52
	Computation time: 8.27666
*)


(* Cases for n=17, Delta=4 *)


(* Choose g1 with maximum degree 4, v1 of degree 4 in g1 *)
createGraphs[17,4,4,4,False,False];

(* Sample results
	List length: 71
	Computation time: 37.0084
*)


(* Choose g1 with maximum degree 3, v1 of degree 3 in g1 *)
createGraphs[17,3,3,4,True,False];

(* Sample results
	List length: 3
	Computation time: 0.32459
*)


(* Cases for n=18, Delta=4 *)


(* Choose g1 with maximum degree 4, v1 of degree 4 in g1 *)
createGraphs[18,4,4,4,False,False];

(* Sample results
	List length: 848
	Computation time: 5752.22
*)


(* Cases with v1 and v2 of different degrees *)
(* Cases for n=18, Delta=5 *)


(* Choose g1 with maximum degree 4, v1 of degree 3 in g1 *)
createGraphs[18,3,4,5,True,True];

(* Sample results
	List length: 993
	Computation time: 3259.24
*)


(* Choose g1 with maximum degree 4, v1 of degree 2 in g1 *)
createGraphs[18,2,4,5,True,True];

(* Sample results
	List length: 504
	Computation time: 586.925
*)


(* Choose g1 with maximum degree 4, v1 of degree 1 in g1 *)
createGraphs[18,1,4,5,True,True];

(* Sample results
	List length: 1138
	Computation time: 87.0919
*)


(* Choose g1 with maximum degree 3, v1 of degree 3 in g1 *)
createGraphs[18,3,3,5,True,True];

(* Sample results
	List length: 153
	Computation time: 44.7778
*)
