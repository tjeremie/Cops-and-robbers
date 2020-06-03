(* ::Package:: *)

(* 
	Generating small 4-cop-win candidate graphs - Part 2 - Filling in the graphs with possible edges
	For Finding the minimum order of 4-cop-win graphs
	By J\[EAcute]r\[EAcute]mie Turcotte and Samuel Yvon
*)


(* Usage
	Option 1 : Run in Mathematica by going to end of file and choosing which computation to run.
	Option 2 : Run in a shell with wolframscript : "wolframscript -script 4copcandidates-part1.wl x x x x x x x x", where x are the desired parameters of fillGraphs.
*)


(* Specify here the path to get the required files for the computation, by default fetches the results online *)
importPathSmallGraphs="https://www.jeremieturcotte.com/research/min4cops/data/smallgraphs/results/3copwingraphs/"; (* The path to the 3-cop-win graphs on fewer vertices, same as in the part 1 of the algorithm. . *)
importPathPart1Results="https://www.jeremieturcotte.com/research/min4cops/data/remainingcases/part1results/graphs/"; (* The path to the results of part 1 of the algorithm. *)


(* CODE *)


(* Debugging function to print a graph with labels *)
printLabel[g_]:=Graph[g,VertexLabels->"Name"]


(* Some functions on neighbourhoods *)
openNeighbourhood[g_,v_]:=AdjacencyList[g,v] (* The neighbourhood of v in g. *)
closedNeighbourhood[g_,v_]:=Prepend[AdjacencyList[g,v],v] (* The closed neighbourhood (includes v) of v in g. *)
noNeighbourhood[g_,v_]:=Complement[VertexList[g],closedNeighbourhood[g,v]] (* The set of vertices of g-N[v]. *)


(* Functions to create and add edges *)
convertToEdge[v_,list_]:=UndirectedEdge[v,#]&/@list (* Returns a list of edges between v and the vertices of list. *)
edgeadd[g_,list_]:=Graph[Join[EdgeList[g],list]] (* Returns the graph g with the added edges of list. This is a substitute for EdgeAdd, as EdgeAdd seems to have some memory leak (as of version 12.1.0.0). *)


(* Functions on the maximum authorized degrees for vertices *)
realDegreeBound[v_,lowerDegreeVerticesList_,maxDeg_]:=maxDeg-Boole[MemberQ[lowerDegreeVerticesList,v]] (* Given maxDeg, which is the maximum authorized degree we consider, and a list of vertices whose degree must be strictly smaller than maxDeg, returns the maximum possible degree of v (either maxDeg or maxDeg-1). *)
viableVertices[g_,v_,lowerDegreeVerticesList_,maxDeg_]:=VertexDegree[g,v]<realDegreeBound[v,lowerDegreeVerticesList,maxDeg] (* Given a graph g and the maximum authorized degree information, returns true if v still has capacity for new neighbour(s).*)


(* Functions to prune out graphs for which the vertices of degree maxDeg do not form a clique (only applied for graphs with v2DegreeGreater>0 *)
specialCleanup[list_,v2DegreeGreater_]:=If[v2DegreeGreater>0,Select[list,graphHubIsClique],list] (* Selects the valid graphs in list. *)
graphHubIsClique[g_]:=CompleteGraphQ[Subgraph[g,GraphHub[g]]] (* Returns True if the vertices of maximum degree of g forms a clique. *)


(* Functions to add possible missing edges *)
newEdgePossibilities[g_,v_,possibleEndVertices_,lowerDegreeVerticesList_,maxDeg_]:=Subsets[Select[possibleEndVertices,viableVertices[g,#,lowerDegreeVerticesList,maxDeg]&],realDegreeBound[v,lowerDegreeVerticesList,maxDeg]-VertexDegree[g,v]](* Given a graph g and a start vertex v, returns the list of possible sets of edges between v and the vertices of possibleEndVertices that can be added while respecting the degree conditions. *)
newGraphPossibilities[g_Graph,v_,possibleEndVertices_,lowerDegreeVerticesList_,maxDeg_,v2DegreeGreater_]:=specialCleanup[edgeadd[g,convertToEdge[v,#]]&/@newEdgePossibilities[g,v,possibleEndVertices,lowerDegreeVerticesList,maxDeg],v2DegreeGreater] (* Given a graph g and a start vertex v, generates the graphs for each possible sets of edges to add. *)
newGraphPossibilities[list_List,v_,possibleEndVertices_,lowerDegreeVerticesList_,maxDeg_,v2DegreeGreater_]:=Flatten[newGraphPossibilities[#,v,possibleEndVertices,lowerDegreeVerticesList,maxDeg,v2DegreeGreater]&/@list] (* Applies the previous function to each graph in list, and brings the resulting list down to one level. *)
iteration[j_,tempList_,lowerDegreeVerticesList_,partition_,maxDeg_,v2DegreeGreater_]:=
	If[j<=Length[partition[[4]]],
		Flatten[newGraphPossibilities[#,partition[[4,j]],Join[partition[[2]],partition[[3]],partition[[4,j+1;;]],partition[[5]]],lowerDegreeVerticesList,maxDeg,v2DegreeGreater]&/@tempList],
		Flatten[newGraphPossibilities[#,partition[[5,j-Length[partition[[4]]]]],partition[[2]],lowerDegreeVerticesList,maxDeg,v2DegreeGreater]&/@tempList]
	]; (* Applies the j-th iteration of the edge-adding procedure : adds edges incident to the j-th neighbour of v2. The possible neighbours change depending on if it is a common neighbour of v1 and v2 or not.  *)


(* Functions to select graphs which have the proper structure *)
validSubgraph[g_,v_,list_]:=MemberQ[list,CanonicalGraph[Subgraph[g,noNeighbourhood[g,v]]]] (* Returns True if g-N[v] is isomorphic to a graph in list. We consider all graphs in list are already in canonical form. *)
validGraph[g_,list_,ignoreVertices_]:=AllTrue[Complement[GraphHub[g],ignoreVertices],validSubgraph[g,#,list]&] (* Returns true if g has the proper form. Does the previous test for every vertex of maximum degree, except for the vertices in the list ignoreVertices, for which we assume this is true (in order not to test what we already know is true). *)


(* Functions to reduce graphs to consider by isomorphism *)
fixedPointsIsomorphism[iso_Association,list_List]:=AllTrue[list,Sort[#/.iso]==Sort[#]&] (* Given an isomorphism iso (encoded as an association) between two graphs on the same set vertices and a list of sets of vertices, returns true if the image (through iso) of every such set of vertices is itself. *)
strongIsomGraphs[g1_Graph,g2_Graph,list_List]:=AnyTrue[FindGraphIsomorphism[g1,g2,All],fixedPointsIsomorphism[#,list]&] (* Given two graphs and a list of sets of vertices, returns true if there exists an isomorphism between g1 and g2 such that the image of every set of vertices is itself (which is what we call a "strong isomorphism"). *)


(* Function to clean and load the list of graphs we are going to merge *)
cleanGraphList[list_]:=Sort[CanonicalGraph/@list,Max[VertexDegree[#1]]>=Max[VertexDegree[#2]]&] (* Returns a cleaned version of list: sorts the graphs by decreasing maximum degree and all graphs in canonical form. *)
loadList[nbVertices_,maxDeg_]:=cleanGraphList[Import[importPathSmallGraphs<>"n"<>ToString[nbVertices]<>"d1D"<>ToString[maxDeg]<>"_3cops.g6","graph6"]] (* Loads the list of 3-cop-win connected graphs on nbVertices vertices such that c(G)=3 with Delta\[LessEqual]maxDeg. *)


(* Main function

	Parameters
		First 6 parameters : The same as in the first 6 parameters of part 1 of the algorithm, will be used to load the appropriate list.
	Optional parameters (otherwise res,mod=1)	
		res: The residue class to compute, between 1 and mod.
		mod: The number of classes in which we split the computation.
		
	Output
		Exports to file a list of candidate 4-cop-win graphs. One file will be generated for each graph produced in part 1 of the algorithm, the graphs are in g6 format.
		Also generates a file which summarizes the computation. On each line there is a list with a variable number of elements: the first element is the index of the base graph, followed by the number of graphs in each part of the algorithm, the last element is the time required for this computation.
*)


fillGraphs[nbTotalVertices_,v1degree_,g1MaximumDegree_,maxDeg_,testAll_,v2DegreeGreater_,res_,mod_]:=
Block[{graphList,baseGraphs,g,partition,lowerDegreeVerticesList,tempList,tempList2,tempList3,outputGraphs,iterationCount,graphCounts,timing,outputFile,counterList,totalTime,totalGraphsGenerated,parameterToFileName},
	(* To convert parameters to string format. *)
	parameterToFileName=ToString[nbTotalVertices]<>"_"<>ToString[v1degree]<>"_"<>ToString[g1MaximumDegree]<>"_"<>ToString[maxDeg]<>"_"<>ToString[testAll]<>"_"<>ToString[v2DegreeGreater];
	
	(* If it does not already exist, we create a directory in which we create the results files. *)
	Quiet[CreateDirectory["finalgraphs_"<>parameterToFileName], CreateDirectory::filex];
	
	(* We load the 3-cop-win graphs, same as in part 1 of the algorithm.*)
	graphList=loadList[nbTotalVertices-maxDeg-1,maxDeg]; 
	
	(* We start by loading the results of the first part of the algorithm. *)
	baseGraphs=Import[importPathPart1Results<>"basegraphs_"<>parameterToFileName<>".mx"];
	
	totalGraphsGenerated=0; (* Will contain the total number of graphs which we have outputed to file. *)
	
	outputFile="./"<>"finalgraphs_"<>parameterToFileName<>"/finalgraphs_"<>parameterToFileName<>If[mod>1,"_part"<>ToString[res],""]<>"_results.txt";
	totalTime=AbsoluteTiming[	
	Do[
		timing=AbsoluteTiming[		
			(* We load a specific base graph. *)
			{g,partition,lowerDegreeVerticesList}=baseGraphs[[i]];
			
			(* Will collect the number of graphs after each step in the algorithm, for debugging and verification purposes. *)
			graphCounts={i};
			
			(* Will contain the graphs after each iteration. *)
			tempList={g};
			
			(* Will count the number of iterations of the edge adding procedure. *)
			iterationCount=0;
			
			Do[
				tempList=iteration[j,tempList,lowerDegreeVerticesList,partition,maxDeg,v2DegreeGreater]; (* Look at possible edges to add to the j-th neighbour of v2. *)
				
				AppendTo[graphCounts,Length[tempList]];
				
				(* 
					We remove graphs which are strongly isomorphic, in the sense that they will give the same graphs later in the algorithm. This can save a significant amount of time and memory.
					As this procedure is itself very lengthy when tempList is large, we only apply it for the 2 first iterations of the edge adding procedure.
					
					We want to see if there exists an isomorphism such that the "classes" of vertices are unchanged.
					At this point in the algorithm, the types are the same as when generating the base graphs, except that we must remember which vertices have already been considered.
					
					As this procedure is itself very lengthy, we only apply it if there are fewer than 40000 graphs in the list. We estimate that for anything more than this it is not worth it.
				*)
				If[Length[tempList]<40000,
					tempList=If[j<=Length[partition[[4]]],
						DeleteDuplicates[tempList,strongIsomGraphs[#1,#2,{partition[[1]],partition[[2]],partition[[3]],partition[[4,1;;j]],partition[[4,j+1;;]],partition[[5]],partition[[6]]}]&]
						,
						DeleteDuplicates[tempList,strongIsomGraphs[#1,#2,{partition[[1]],partition[[2]],partition[[3]],partition[[4]],partition[[5,1;;j-Length[partition[[4]]]]],partition[[5,j-Length[partition[[4]]]+1;;]],partition[[6]]}]&]
					];
				];
				
				AppendTo[graphCounts,Length[tempList]];
				
				,{j,1,2}
			];
			
			counterList=ConstantArray[0,maxDeg-2]; (* Will contain the number of graphs after each of the next few iterations.*)
			
			(* To save memory, we split up the next few iterations. We do it separately for each graph resulting of the 2 first iterations. *)
			outputGraphs=Flatten[Reap[
				Do[
					tempList2={g2};
					
					Do[
						tempList2=iteration[j,tempList2,lowerDegreeVerticesList,partition,maxDeg,v2DegreeGreater];
						counterList[[j-2]]+=Length[tempList2];
						
						,{j,3,maxDeg-1}
					];
					
					(* For the last iteration, to save memory, we do not need to save the graphs for later iterations. We only save the graphs which we consider possible candidate 4-cop-win graphs. *)
					Do[
						tempList3=newGraphPossibilities[g3,partition[[5,-1]],partition[[2]],lowerDegreeVerticesList,maxDeg,v2DegreeGreater];
						counterList[[-1]]+=Length[tempList3];
						
						(* The viable candidate graphs are those such that for each vertex u of maximum degree, g-N[u] is in graphList (and further down in the list without loss of generality). *)
						Sow[CanonicalGraph/@Select[tempList3,validGraph[#,graphList,{partition[[1,1]],partition[[6,1]]}]&]];
						
						tempList3={};
						
						,{g3,tempList2}
					];
					
					tempList2={};
					,{g2,tempList}
				]
			][[2]]];
			
			graphCounts=Join[graphCounts,counterList]; (* We merge the counts. *)
			AppendTo[graphCounts,Length[outputGraphs]]; (* We append the number of graphs we output. *)
		
			(* We now remove all isomorphic graphs. *)
			outputGraphs=DeleteDuplicates[outputGraphs];
			AppendTo[graphCounts,Length[outputGraphs]];
			
			totalGraphsGenerated+=Length[outputGraphs];
			][[1]];
			
			AppendTo[graphCounts,timing];
			
			(* We export the results. *)
			PutAppend[graphCounts,outputFile];
			Export["./"<>"finalgraphs_"<>parameterToFileName<>"/finalgraphs_"<>parameterToFileName<>"_"<>ToString[i]<>".g6",outputGraphs,"Graph6"];
			
		, {i,res,Length[baseGraphs],mod} (* We do the computation for each choice of graph (in the proper modulo class) from part 1 of the algorithm. *)
	];
	][[1]];
	
	PutAppend[{Total,totalGraphsGenerated,totalTime},outputFile];
]
fillGraphs[nbTotalVertices_,v1degree_,g1MaximumDegree_,maxDeg_,testAll_,v2DegreeGreater_]:=fillGraphs[nbTotalVertices,v1degree,g1MaximumDegree,maxDeg,testAll,v2DegreeGreater,1,1] (* Version of the function with only one part. *)


fillGraphs@@(ToExpression/@$ScriptCommandLine[[2;;]]) (* For calls from a shell. Otherwise, call fillGraphs with the desired parameters. *)
