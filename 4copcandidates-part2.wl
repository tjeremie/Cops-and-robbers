(* ::Package:: *)

(* 
	Generating small 4-cop-win candidate graphs - Part 2
	For Finding the minimum order of 4-cop-win graphs
	By J\[EAcute]r\[EAcute]mie Turcotte and Samuel Yvon
*)


(* Usage
	Go to end of file and choose which computation to run.
	
	Either execute in Mathematica or in terminal with "wolfram -script 4copcandidates-part2.wl".	

	Note : Computations are often long and some use a lot of memory.
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


(* Functions on the maximum authorized degrees for vertices *)
realDegreeBound[v_,lowerDegreeVerticesList_,maxDeg_]:=maxDeg-Boole[MemberQ[lowerDegreeVerticesList,v]] (* Given maxDeg, which is the maximum authorized degree we consider, and a list of vertices whose degree must be strictly smaller than maxDeg, returns the maximum possible degree of v (either maxDeg or maxDeg-1). *)
viableVertices[g_,v_,lowerDegreeVerticesList_,maxDeg_]:=VertexDegree[g,v]<realDegreeBound[v,lowerDegreeVerticesList,maxDeg] (* Given a graph g and the maximum authorized degree information, returns true if v still has capacity for new neighbour(s).*)


(* Functions to add possible missing edges *)
newEdgePossibilities[g_,v_,possibleEndVertices_,lowerDegreeVerticesList_,maxDeg_]:=convertToEdge[v,#]&/@Subsets[Select[possibleEndVertices,viableVertices[g,#,lowerDegreeVerticesList,maxDeg]&],realDegreeBound[v,lowerDegreeVerticesList,maxDeg]-VertexDegree[g,v]](* Given a graph g and a start vertex v, returns the list of possible sets of edges between v and the vertices of possibleEndVertices that can be added while respecting the degree conditions. *)
newGraphPossibilities[g_Graph,v_,possibleEndVertices_,lowerDegreeVerticesList_,maxDeg_]:=EdgeAdd[g,#]&/@newEdgePossibilities[g,v,possibleEndVertices,lowerDegreeVerticesList,maxDeg] (* Given a graph g and a start vertex v, generates the graphs for each possible sets of edges to add. *)
newGraphPossibilities[list_List,v_,possibleEndVertices_,lowerDegreeVerticesList_,maxDeg_]:=Flatten[newGraphPossibilities[#,v,possibleEndVertices,lowerDegreeVerticesList,maxDeg]&/@list] (* Applies the previous function to each graph in list, and brings the resulting list down to one level *)


(* Functions to select graphs which have the proper structure *)
validSubgraph[g_,v_,list_]:=MemberQ[list,CanonicalGraph[Subgraph[g,noNeighbourhood[g,v]]]] (* Returns True if g-N[v] is isomorphic to a graph in list. We consider all graphs in list are already in canonical form. *)
validGraph[g_,list_,ignoreVertices_]:=AllTrue[Complement[GraphHub[g],ignoreVertices],validSubgraph[g,#,list]&] (* Returns true if g has the proper form. Does the previous test for every vertex of maximum degree, except for the vertices in the list ignoreVertices, for which we assume this is true (in order not to test what we already know is true). *)


(* Functions to reduce graphs to consider by isomorphism *)
fixedPointsIsomorphism[iso_Association,list_List]:=AllTrue[list,Sort[#/.iso]==Sort[#]&] (* Given an isomorphism iso (encoded as an association) between two graphs on the same set vertices and a list of sets of vertices, returns true if the image (through iso) of every such set of vertices is itself. *)
strongIsomGraphs[g1_Graph,g2_Graph,list_List]:=AnyTrue[FindGraphIsomorphism[g1,g2,All],fixedPointsIsomorphism[#,list]&] (* Given two graphs and a list of sets of vertices, returns true if there exists an isomorphism between g1 and g2 such that the image of every set of vertices is itself (which is what we call a "strong isomorphism"). *)


(* Main function

	Parameters
		First 6 parameters: Use same parameters as in part 1 of the algorithm, will be used to load the appropriate list.
		res: The residue class to compute (between 1 and mod).
		mod: The number of classes in which
		
	Output
		Exports to file a list of candidate 4-cop-win graphs. One file will be generated for each base graph used.
		Also creates a file which lists the number of graphs in each step of the algorithm.

	Note
		For simplicity of usage, this function requires internet access to fetch the results of the part 1 of the algorithm. One could also download the files and read them directly.
		All files will be created in the same directory as the script.
*)


completeGraphs[nbTotalVertices_,v1degree_,g1MaximumDegree_,maxDeg_,testAll_,v2DegreeGreater_,res_,mod_]:=
Block[{graphList,baseGraphs,g,partition,lowerDegreeVerticesList,index,tempList,tempList2,counter,iterationCount,graphCounts},
	(* We start by loading the results of the first part of the algorithm. *)
	{graphList,baseGraphs}=Import["https://www.jeremieturcotte.com/research/4copsdata/remainingcases/graphs/part1/basegraphs_"<>ToString[nbTotalVertices]<>"_"<>ToString[v1degree]<>"_"<>ToString[g1MaximumDegree]<>"_"<>ToString[maxDeg]<>"_"<>ToString[testAll]<>"_"<>ToString[v2DegreeGreater]<>".mx"];
	
	(* Even if graphs in graphList are already in canonical form (done in part 1), due to a bug we need to reapply the canonical labelling. *)
	graphList=CanonicalGraph/@graphList;
	
	AbsoluteTiming[
		Do[
			(* We load a specific base graph. *)
			g=baseGraphs[[i,1]];
			partition=baseGraphs[[i,2]];
			lowerDegreeVerticesList=baseGraphs[[i,3]];
			index=baseGraphs[[i,4]];
			
			(* Will collect the number of graphs after each step in the algorithm, for debugging and verirication purposes. *)
			graphCounts={i};
			
			(* Will contain the graphs after each iteration. *)
			tempList={g};
			
			(* Will count the number of iterations of the edge adding procedure. *)
			iterationCount=0;
			
			(* For each vertex in partition[[4]] (the common neighbours of v1 and v2), we add possible edges. *)
			Do[
				iterationCount++;
				
				(* We add the possible new edges for the j-th vertex of partition[[4]]. *)
				tempList=Flatten[newGraphPossibilities[#,partition[[4,j]],Join[partition[[2]],partition[[3]],partition[[4,j+1;;]],partition[[5]]],lowerDegreeVerticesList,maxDeg]&/@tempList];
				
				(* 
					We remove graphs which are strongly isomorphism, in the sense that they will give the same graphs later in the algorithm. This can save a significant amount of time and memory.
					As this procedure is itself very lengthy when tempList is large, we only apply it for the 2 first iterations.
					
					We want to see if there exists an isomorphism such that the "types" of vertices are unchanged.
					At this point in the algorithm, the types are the same as when generating the base graphs, except that we must distinguish the vertices of partition[[4]] for which the new edges have already been added or are yet to be added.
				*)
				If[iterationCount<=2,
					tempList=DeleteDuplicates[tempList,strongIsomGraphs[#1,#2,{partition[[1]],partition[[2]],partition[[3]],partition[[4,1;;j]],partition[[4,j+1;;]],partition[[5]],partition[[6]]}]&];
				];
			
				AppendTo[graphCounts,Length[tempList]];
				
				,{j, 1, Length[partition[[4]]]}
			];
			
			(* We do the same operations for the vertices in partition[[5]] (neighbours of v2 but not of v1), except for one. *)
			Do[
				iterationCount++;
				
				tempList=Flatten[newGraphPossibilities[#,partition[[5,j]],partition[[2]],lowerDegreeVerticesList,maxDeg]&/@tempList];
				
				If[iterationCount<=2,
					tempList=DeleteDuplicates[tempList,strongIsomGraphs[#1,#2,{partition[[1]],partition[[2]],partition[[3]],partition[[4]],partition[[5,1;;j]],partition[[5,j+1;;]],partition[[6]]}]&];
				];
			
				AppendTo[graphCounts,Length[tempList]];
				
				,{j, 1, Length[partition[[5]]]-1}
			];
			
			
			(* In order to save memory, during the last iteration we do not save the complete list of graphs we create, only those we consider to be viable candidates. *)
			counter=0;
			tempList=Flatten[Reap[
				Do[
					tempList2=newGraphPossibilities[g,partition[[5,-1]],partition[[2]],lowerDegreeVerticesList,maxDeg];
					counter=counter+Length[tempList2];
				
					(* The viable candidate graphs are those such that for each vertex u of maximum degree, g-N[u] is in graphList (and further down in the list without loss of generality). *)
					Sow[Select[tempList2,validGraph[#,graphList[[index;;]],{partition[[1,1]],partition[[6,1]]}]&]]

					,{g,tempList}
				];
			][[2]]];
		
			AppendTo[graphCounts,counter];
			AppendTo[graphCounts,Length[tempList]];
		
			(* We now remove all isomorphic graphs. *)
			tempList=DeleteDuplicates[CanonicalGraph/@ tempList];
			
			AppendTo[graphCounts,Length[tempList]];
		
			(* We export the results. *)
			graphCounts>>>NotebookDirectory[]<>"part2results_"<>ToString[nbTotalVertices]<>"_"<>ToString[v1degree]<>"_"<>ToString[g1MaximumDegree]<>"_"<>ToString[maxDeg]<>"_"<>ToString[testAll]<>"_"<>ToString[v2DegreeGreater]<>".txt";
			Export[NotebookDirectory[]<>"finalgraph_"<>ToString[nbTotalVertices]<>"_"<>ToString[v1degree]<>"_"<>ToString[g1MaximumDegree]<>"_"<>ToString[maxDeg]<>"_"<>ToString[testAll]<>"_"<>ToString[v2DegreeGreater]<>"_"<>ToString[i]<>".g6",tempList,"Graph6"];
			
			,{i,res,Length[baseGraphs],mod}
		];
	][[1]]>>>NotebookDirectory[]<>"part2results_"<>ToString[nbTotalVertices]<>"_"<>ToString[v1degree]<>"_"<>ToString[g1MaximumDegree]<>"_"<>ToString[maxDeg]<>"_"<>ToString[testAll]<>"_"<>ToString[v2DegreeGreater]<>"_mod"<>ToString[mod]<>".txt"; (* This exports the total computation time. *)
]


(* COMPUTATION *)


completeGraphs[18,3,3,5,True,True,1,1] (* example command *)
