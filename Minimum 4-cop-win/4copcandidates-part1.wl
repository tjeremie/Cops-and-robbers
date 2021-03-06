(* ::Package:: *)

(* ::Input:: *)
(**)


(* ::Subtitle:: *)
(*Generating small 4-cop-win candidate graphs *)
(*Part 1/2 - Generating the base graphs*)
(*For Finding the minimum order of 4-cop-win graphs*)
(*By J\[EAcute]r\[EAcute]mie Turcotte and Samuel Yvon*)


(* ::Subtitle:: *)
(*Usage*)
(*	Option 1 : Run in Mathematica by going to end of file and choosing which computation to run.*)
(*	Option 2 : Run in a shell with wolframscript : "wolframscript -script 4copcandidates-part1.wl x x x x x x", where x are the desired parameters of createGraphs.*)


(* Specify here the path to get the lists of 3-cop-win graphs, by default fetches the results online *)
importPath="https://www.jeremieturcotte.com/research/min4cops/data/smallgraphs/results/3copwingraphs/";


(* ::Subtitle:: *)
(*Code:*)


(* Debugging function to print a graph with labels *)

printLabel[g_]:=Graph[g,VertexLabels->"Name"]


(* Some functions on neighbourhoods *)

(* The neighbourhood of v in g. *)
openNeighbourhood[g_,v_]:=AdjacencyList[g,v] 
(* The closed neighbourhood (includes v) of v in g. *)
closedNeighbourhood[g_,v_]:=Prepend[AdjacencyList[g,v],v] 
(* The set of vertices of g-N[v]. *)
noNeighbourhood[g_,v_]:=Complement[VertexList[g],closedNeighbourhood[g,v]]


(* Functions to create formal edges *)

(* Returns a list of edges between v and the vertices of list. *)
convertToEdge[v_,list_]:=UndirectedEdge[v,#]&/@list 
(* Returns a list of edges between the vertices in list and v1 and with v2. *)
doubleConvertToEdge[v1_,v2_,list_]:=Join[convertToEdge[v1,list],convertToEdge[v2,list]] 


(* Functions to reduce vertices to consider by automorphism *)


(* Given a list of automorphisms (encoded as associations) of some graph, returns all
   vertices equivalent to v through one of these automorphisms. *)
automorphismsImage[automorphismList_,v_]:=Union[Map[#[v]&,automorphismList]] 

(* Given a graph g and a vertex v, returns all vertices equivalent to v through some automorphism of g. *)
automorphicEquivalentVertices[g_,v_]:=automorphismsImage[FindGraphIsomorphism[g,g,All],v]

(* Given a graph g and a list of vertices of g, removes from this list vertices which are equivalent through some automorphism. *)
reduceByAutomorphism[g_,list_]:=DeleteDuplicates[list,MemberQ[automorphicEquivalentVertices[g,#1],#2]&] 

(* Given a graph g, returns a list of vertices of chosen degree, all of which are not equivalent by automorphism. 
   This function is currently with memory to save computation time. *)
reducedVertexChoices[g_,degree_]:=(reducedVertexChoices[g,degree]=reduceByAutomorphism[g,selectDegreeVertices[g,degree]]) 


(* Functions relating to the maximum authorized possible degree of vertices *)

(* Given maxDeg, which is the maximum authorized degree we consider, and a list of vertices whose degree must be strictly smaller than maxDeg,
   returns the maximum possible degree of v (either maxDeg or maxDeg-1). *)
realDegreeBound[v_,lowerDegreeVerticesList_, maxDeg_]:=maxDeg-Boole[MemberQ[lowerDegreeVerticesList,v]]

(* Verifies if the maximum degree of g is at most maxDeg and all vertices in lowerDegreeVerticesList have strictly smaller degree.
   If true, returns g, otherwise returns Nothing (an element which vanishes in any list). *)
degreesFilter[g_,lowerDegreeVerticesList_,maxDeg_]:=If[AllTrue[VertexList[g],VertexDegree[g,#]<=realDegreeBound[#,lowerDegreeVerticesList,maxDeg] &],g,Nothing] 


(* Functions to reduce graphs to consider by isomorphism *)


(* Given an isomorphism iso (encoded as an association) between two graphs on the same set vertices and a list of sets of vertices,
   returns true if the image (through iso) of every such set of vertices is itself. *)
fixedPointsIsomorphism[iso_,list_]:=AllTrue[list,Sort[#/.iso]==Sort[#]&] 

(* Given two graphs and a list of sets of vertices, returns true if there exists an isomorphism between g1 and g2 such that the image
   of every set of vertices is itself (which is what we call a "strong isomorphism"). *)
strongIsomGraphs[g1_,g2_,list_]:=AnyTrue[FindGraphIsomorphism[g1,g2,All],fixedPointsIsomorphism[#,list]&]


(* Functions used in the labelling of new vertices *)


(* The list of vertices that will need to be added as common neighbors of v1 and v2 when merging the graphs. *)
verticesToAdd[g2_,v2_,maxDeg_,nbInteriorVertices_]:=nbInteriorVertices+Range[maxDeg-VertexDegree[g2,v2]] 

(* The list of labels we will give to the current neighbours of v2 when merging the graphs. *)
alreadyNeighbours[g2_,v2_,maxDeg_,nbTotalVertices_]:=nbTotalVertices-Range[VertexDegree[g2,v2]] 

(* The six classes of vertices in the merged graph g, as described in the proof. *)
graphSections[g1_,v1_,g2_,v2_,maxDeg_,nbTotalVertices_]:={{v1},openNeighbourhood[g1,v1],noNeighbourhood[g1,v1],verticesToAdd[g2,v2,maxDeg,VertexCount[g1]],alreadyNeighbours[g2,v2,maxDeg,nbTotalVertices],{nbTotalVertices}} 


(* Functions to merge graphs g1 and g2 relative to a choice of v1 and v2 *)

(* Deletes in list the graphs not respecting the authorized degrees and removes graphs which are strongly isomorphic.
   It is important to note that it would technically also be necessary to verify that this isomorphism is compatible with
   the list of degrees which must have degree strictly smaller than maxDeg. But as we use our strong isomorphisms to,
   in particular, fix g1, the restriction of the isomorphism will also be an automorphism of g1,
   and as equivalent vertices have the same degree bounds, this is valid.
 *)
removeIsoAndClean[list_,g1_,v1_,g2_,v2_,lowerDegreeVerticesList_,maxDeg_,nbTotalVertices_]:=DeleteDuplicates[degreesFilter[#,lowerDegreeVerticesList,maxDeg]&/@list,strongIsomGraphs[#1,#2,graphSections[g1,v1,g2,v2,maxDeg,nbTotalVertices]]&] 

(* Lists all isomorphisms (encoded as associations) from g2-N[v2] to g1-N[v1]. *)
subgraphIsomorphisms[g1_,v1_,g2_,v2_]:=FindGraphIsomorphism[Subgraph[g2,noNeighbourhood[g2,v2]],Subgraph[g1,noNeighbourhood[g1,v1]],All]  

(* Merge graphs g1 and g2 with the following rules. Keep the numbering of g1, relabel v2 and it's neighbourhood
   respectively with labels nbVertices and nbVertices-1 to nbVertices-d_g2(v2). Relabel g2-N[v2] using the isomorphism iso 
   (which is an isomorphism between g2-N[v2] and g1-N[v1]) to be able to merge with g1. If d_g2(v2)<maxDeg, add common neighbors
   to v1 and v2 to bring v2 to maximum degree. 
 *)
mergeGraphsWithSpecificIso[g1_,v1_,g2_Graph,v2_,iso_,maxDeg_,nbTotalVertices_]:=EdgeAdd[GraphUnion[g1,VertexReplace[g2,Join[Normal[iso],
						  Table[closedNeighbourhood[g2,v2][[i]]->nbTotalVertices-i+1,{i,VertexDegree[g2,v2]+1}]]]],doubleConvertToEdge[v1,nbTotalVertices,verticesToAdd[g2,v2,maxDeg,VertexCount[g1]]]] 

(* Merge graphs g1 and g2 as above, by considering every possible way of merging g1-N[v1] and g2-N[v2]. 
   Also adds to every graph relevant information for the next part of the algorithm (which is adding possible missing edges).
 *)
mergeGraphs[g1_,v1_,g2_,v2_,lowerDegreeVerticesList_,maxDeg_,nbTotalVertices_]:={#,graphSections[g1,v1,g2,v2,maxDeg,nbTotalVertices],
           lowerDegreeVerticesList}&/@removeIsoAndClean[mergeGraphsWithSpecificIso[g1,v1,g2,v2,#,maxDeg,nbTotalVertices]&/@subgraphIsomorphisms[g1,v1,g2,v2],g1,v1,g2,v2,lowerDegreeVerticesList,maxDeg,nbTotalVertices] 


(* Functions to choose vertices depending on degree *)

(* Returns all vertices of degree deg in g. *)
selectDegreeVertices[g_,deg_]:=Select[VertexList[g],VertexDegree[g,#]==deg&] 

(* Returns all vertices of degree greater than deg in g.*)
selectUpperDegreeVertices[g_,deg_]:=Select[VertexList[g],VertexDegree[g,#]>deg&]


(* Function to clean and load the list of graphs we are going to merge *)

(* Returns a cleaned version of list: sorts the graphs by decreasing maximum degree and all graphs in canonical form. *)
cleanGraphList[list_]:=Sort[CanonicalGraph/@list,Max[VertexDegree[#1]]>=Max[VertexDegree[#2]]&] 

(* Loads the list of 3-cop-win connected graphs on nbVertices vertices such that c(G)=3 with Delta\[LessEqual]maxDeg. *)
loadList[nbVertices_,maxDeg_]:=cleanGraphList[Import[importPath<>"n"<>ToString[nbVertices]<>"d1D"<>ToString[maxDeg]<>"_3cops.g6","graph6"]] 


(* ::Text:: *)
(*Main function*)
(*	Parameters*)
(*		nbTotalVertices: The total number of vertices in the graphs we will create.*)
(*		v1degree: The degree of the vertices v1 we will choose in g1.*)
(*		g1MaximumDegree: The maximum degree of the graphs g1 we will choose.*)
(*		maxDeg: The maximum degree of the graphs we will create.*)
(*		testAll: If True, graphs will be created for each possible choice of v1 in g1, otherwise will be done for one choice of v1.*)
(*		v2DegreeGreater: The degree of v2 will be set to v1Degree+v2DegreeGreater. If v2DegreeGreater>0, we suppose that g-N[v1] has maximum degree 4. Only works if nbTotalVertices=18 vertices and maxDeg=5.*)
(*	Optional parameters (otherwise res=mod=1)*)
(*		res: The part of the computation to do, between 1 and mod.*)
(*		mod: The number of parts to split the computation in.*)
(**)
(*	Output*)
(*		Exports to file a list where each item is itself a list of length 3:*)
(*			The first item is the created base graph.*)
(*			The second item is the breakdown into the 6 types of vertices of the graph.*)
(*			The third item is the list of vertices which must have maximum degree strictly smaller than maxDeg, this is useful to reduce the number of cases in part 2 of the algorithm.*)
(*		Also creates a file which summarizes the computation. On each line there is a list of length 3: the index of g1 in the (cleaned-up and reordered) list, the number of graph created from this choice of g1 and the time required for this computation.*)


createGraphs[nbTotalVertices_,v1degree_,g1MaximumDegree_,maxDeg_,testAll_,v2DegreeGreater_,res_,mod_]:=
Block[{graphList1,graphList2,start,end,g1,v1,lowerDegreeVerticesList,reducedVerticesToConsider,results,v2degree,totalTime,outputFile,temp},
	(* File that will contain an outline of the results of the computation.*)
	outputFile="basegraphs_"<>ToString[nbTotalVertices]<>"_"<>ToString[v1degree]<>"_"<>ToString[g1MaximumDegree]<>"_"<>ToString[maxDeg]<>"_"<>ToString[testAll]<>"_"<>ToString[v2DegreeGreater]<>"_results"<>If[mod>1,"_part"<>ToString[res],""]<>".txt";
	
	totalTime=AbsoluteTiming[
		(* We load the list of graphs in which we pick g1. *)
		graphList1=loadList[nbTotalVertices-maxDeg-1,maxDeg]; 
		
		(* This will be the degree of v2 in g2. *)
		v2degree=v1degree+v2DegreeGreater;
		
		(* We load the list of graphs in which we pick g2. *)
		graphList2=If[v2DegreeGreater>0,loadList[12+v2DegreeGreater,4],graphList1];
	
		(* We select the start and the end indices of all graphs with maximum degree exactly g1MaximumDegree in graphList. *)
		start=FirstPosition[graphList1,_?(Max[VertexDegree[#]]==g1MaximumDegree&)][[1]];
		end=Length[graphList1]+1-FirstPosition[Reverse[graphList1],_?(Max[VertexDegree[#]]==g1MaximumDegree&)][[1]];
	
		results=Flatten[
			Table[
				If[Mod[i-res,mod]==0,
					(* For each possible graph g1 with maximum degree exactly g1MaximumDegree, we will also reduce by automorphism the possible choices of v1. *)
					g1=graphList1[[i]];
					reducedVerticesToConsider=reducedVertexChoices[g1,v1degree];
			
					temp=AbsoluteTiming[Flatten[Table[
							(* We choose a vertex v1. *)
							v1=reducedVerticesToConsider[[j]];
					
							(* All vertices which either come before v1 in reducedVerticesToConsider or which have higher degree than v1 are considered to already having been verified, so have degree strictly smaller than maxDeg. *)
							lowerDegreeVerticesList=If[v2DegreeGreater>0,Range[12],Union[Flatten[Table[automorphicEquivalentVertices[g1,reducedVerticesToConsider[[k]]],{k,1,j-1}]],selectUpperDegreeVertices[g1,v1degree]]];
				
							(* For some choice of g2,v2, we compute the merged list. *)
							mergeGraphs[g1,v1,g2,v2,lowerDegreeVerticesList,maxDeg,nbTotalVertices]
	
						 (* We choose v2 up to automorphism. *)
						,{j,1,If[testAll,Length[reducedVerticesToConsider],Boole[Length[reducedVerticesToConsider]>0]]},{g2,graphList2},{v2,reducedVertexChoices[g2,v2degree]}
					],3]];
					
					PutAppend[{i,Length[temp[[2]]],temp[[1]]},outputFile];
					
					temp[[2]]
					
					, Nothing
				]
				
				,{i,start,end} (* The index of g1 in the list. *)
			]
			,1 (* We flatten 4 layers as there are 4 levels in our table. *)
		];
	
		Export["basegraphs_"<>ToString[nbTotalVertices]<>"_"<>ToString[v1degree]<>"_"<>ToString[g1MaximumDegree]<>"_"<>ToString[maxDeg]<>"_"<>ToString[testAll]<>"_"<>ToString[v2DegreeGreater]<>If[mod>1,"_part"<>ToString[res],""]<>".mx",results]
	][[1]];
	
	PutAppend[{Total, Length[results],totalTime},outputFile];
]
createGraphs[nbTotalVertices_,v1degree_,g1MaximumDegree_,maxDeg_,testAll_,v2DegreeGreater_]:=createGraphs[nbTotalVertices,v1degree,g1MaximumDegree,maxDeg,testAll,v2DegreeGreater,1,1] (* Version of the function with only one part. *)


createGraphs@@(ToExpression/@$ScriptCommandLine[[2;;]]) (* For calls from a shell. Otherwise, call createGraphs with the desired parameters. *)



