#=
    Algorithm for testing cop numbers 1,2,3
    By Jérémie Turcotte

    Algorithm inspired by those suggested, for example, in https://math.ryerson.ca/~abonato/papers/distcops_bcp030109.pdf and https://www.sciencedirect.com/science/article/pii/S0012365X12000064.

    Also includes an example of how to scan various files of graphs, in the g6 format, for which to breakdown the number of graphs of each cop number.

    As codes for the various cop numbers are very similar, we only comment the code for cop number 2.
=#


using LightGraphs, GraphIO, Base

# Returns true if the line i in mat (of size n^2) is all true
function convertToBool1(mat,i)
    return !(false in mat[i,:])
end

# Returns true if the line ij in mat (of size n^3) is all true
function convertToBool2(mat,i,j)
    return !(false in mat[i,j,:])
end

# Returns true if the line ijl in mat (of size n^4) is all true
function convertToBool3(mat,i,j,l)
    return !(false in mat[i,j,l,:])
end

# Returns true if c(G)=1, false if c(G)>1
function oneCopWin(g)
    n=nv(g)
    configs=falses(n,n)
    queued=trues(n)
    
    for i in 1:n
        for k in 1:n
            templist=vcat(neighbors(g,k),k)
            if i in templist
                configs[i,k]=true
            end
        end
    end

    for i in 1:n
        if (convertToBool1(configs,i))
            return true
        end 
    end
    
    bigchange=true
    
    while bigchange
        bigchange=false
        
        for i in 1:n
            if queued[i]
                queued[i]=false
                for ip in vcat(neighbors(g,i),i)

                    changed=false

                    for kp in 1:n
                        if !configs[ip,kp]
                            temp=true

                            for k in vcat(neighbors(g,kp),kp)
                                if !configs[i,k]
                                    temp=false
                                    break
                                end
                            end

                            if temp
                                configs[ip,kp]=true
                                changed=true
                                
                                if (convertToBool1(configs,ip))
                                    return true
                                end
                            end
                        end
                    end

                    if changed
                        queued[ip]=true
                        bigchange=true
                    end
                end
            end
        end
    end
    
    return false
end

# Returns true if c(G)<=2, false if c(G)>2
function twoCopWin(g)
    n=nv(g) # number of vertices in g

    configs=falses(n,n,n)
    #=
        At any given moment in the code, configs[i,j,k] will be true if we know that there is a strategy to win if there are cops on i and j and a robber on k (and it is cops' turn).
        Will be false if either we do not know yet, or there is no winning strategy in that position (which is why we start by initializing the array to all false).
        The idea of the algorithm is to progressively fill up the matrix by finding new winning strategies, going backwards starting from the final turn.
    =#

    queued=trues(n,n) # Will represent the positions (i,j) that think we should verify soon. We start by deeming all positions interesting.

    # If either i or j is in the neighbourhood of k, then with cops on i and j, a robber on k will immediately be caught.
    for i in 1:n
        for j in 1:i
            for k in 1:n
                templist=vcat(neighbors(g,k),k)
                if i in templist || j in templist
                    configs[i,j,k]=true
                    configs[j,i,k]=true # To not repeat the same calculations, we only chose j between 1 and i : the order of (i,j) does not matter.
                end
            end
        end
    end
    
    # If there exists a choice of starting positions (i,j) for the cops such that for any choice of robber position k there is a winning strategy, then 2 cops can win.
    # Checking this now amounts to verifying if there is a dominating set of size 2 in the graph. 
    for i in 1:n
        for j in 1:i
            if (convertToBool2(configs,i,j))
                return true
            end 
        end
    end
    
    bigchange=true
    
    while bigchange # If the matrix did not see any change in the last iteration, then there will not be any further change at any time: 2 cops cannot win.
        bigchange=false
        
        for i in 1:n
            for j in 1:i
                if queued[i,j] # Suppose we consider (i,j) to be an interesting position: either because we are in the start of the algorithm or because for some k mat[i,j,k] changed value recently, and we want to see if this impacts neighbouring positions.

                    queued[i,j]=false

                    for ip in vcat(neighbors(g,i),i), jp in vcat(neighbors(g,j),j) # We choose (ip,jp) such that cops can move to (i,j) in 1 turn.

                        changed=false

                        for kp in 1:n # We consider every possible position for the robber

                            if !configs[ip,jp,kp] # We only need to consider those kp such that we don't already know gives a winning position
                                temp=true

                                for k in vcat(neighbors(g,kp),kp) # We consider the vertices k that the robber can move to from kp
                                    if !configs[i,j,k] # If there is a vertex k where the robber can go such that the move (ip,jp)->(i,j) does not yield a winning position, we cannot say anything new.
                                        temp=false
                                        break
                                    end
                                end

                                if temp # Otherwise, if the move (ip,jp)->(i,j) gives a winning position whatever the robber does (for every choice of k), we know that (ip,jp,kp) is a winning position.
                                    configs[ip,jp,kp]=true
                                    configs[jp,ip,kp]=true
                                    
                                    if (convertToBool2(configs,ip,jp)) # We verify if this gives us a winning starting position (ip,jp), if so we are done.
                                        return true
                                    end
                                    
                                    changed=true # Indicates that at least one triple (ip,jp,kp) has changed value.
                                end
                            end
                        end

                        if changed # If at least one triple (ip,jp,kp) changed value, then we deem that (ip,jp) might be interesting : this means we may "be ready" to find winning strategies for neighbour positions.
                            queued[ip,jp]=true
                            queued[jp,ip]=true
                            bigchange=true
                        end
                    end
                end
            end
        end
    end
    
    return false
end

# Returns true if c(G)<=3, false if c(G)>3
function threeCopWin(g)
    n=nv(g)
    configs=falses(n,n,n,n)
    queued=trues(n,n,n)

    for i in 1:n
        for j in 1:i
            for l in 1 : j
                for k in 1:n
                    templist=vcat(neighbors(g,k),k)
                    if i in templist || j in templist || l in templist
                        configs[i,j,l,k]=true
                        configs[j,i,l,k]=true
                        configs[i,l,j,k]=true
                        configs[j,l,i,k]=true
                        configs[l,i,j,k]=true
                        configs[l,j,i,k]=true
                    end
                end
            end
        end
    end
    
    for i in 1:n
        for j in 1:i
            for k in 1:j
                if (convertToBool3(configs,i,j,k))
                    return true
                end 
            end
        end
    end

    bigchange=true

    while bigchange
        bigchange=false
        
        for i in 1:n
            for j in 1:i
                for l in 1:j
                    if queued[i,j,l]
                        queued[i,j,l]=false
                        for ip in vcat(neighbors(g,i),i), jp in vcat(neighbors(g,j),j), lp in vcat(neighbors(g,l),l)

                            changed=false

                            for kp in 1:n
                                if !configs[ip,jp,lp,kp]
                                    temp=true

                                    for k in vcat(neighbors(g,kp),kp)
                                        if !configs[i,j,l,k]
                                            temp=false
                                            break
                                        end
                                    end

                                    if temp
                                        configs[ip,jp,lp,kp]=true
                                        configs[jp,ip,lp,kp]=true
                                        configs[ip,lp,jp,kp]=true
                                        configs[jp,lp,ip,kp]=true
                                        configs[lp,ip,jp,kp]=true
                                        configs[lp,jp,ip,kp]=true

                                        changed=true
                                        
                                        if (convertToBool3(configs,ip,jp,lp))
                                            return true
                                        end
                                    end
                                end
                            end

                            if changed
                                queued[ip,jp,lp]=true
                                queued[jp,ip,lp]=true
                                queued[ip,lp,jp]=true
                                queued[jp,lp,ip]=true
                                queued[lp,ip,jp]=true
                                queued[lp,jp,ip]=true
                                bigchange=true
                            end
                        end
                    end
                end
            end
        end
    end
    
    return false
end

# Example of function to load a file of graphs in the graph6 format
function loadList(i,nbfiles,n)
    try
        return collect(values(loadgraphs(string("./n",n,"/graphs_",n,"_1_",n,"_",i,"_",nbfiles,".g6"), GraphIO.Graph6.Graph6Format())));
    catch BoundsError
        return []
    end
end

#=
    Example of function to manage reading each file and breaking down the cop numbers

    Will print the breakdown of the cop numbers of the graphs and will save the graphs needing 3 and 4 cops in files

    This example supports multithreading, see https://julialang.org/blog/2019/07/multithreading/ to change the number of threads.
    Experimentally, speedup of almost factor 2 between 1 and 2 threads but does not improve much after 4 threads.
=#

function fctThreaded(nbfiles,n)
    totalonecopcount=0
    totaltwocopcount=0
    totalthreecopcount=0
    totalfourcopcount=0

    d3=Dict{AbstractString,AbstractGraph}()
    d4=Dict{AbstractString,AbstractGraph}()

    for i in 0:(nbfiles-1)

        localonecopcount=Threads.Atomic{Int}(0)
        localtwocopcount=Threads.Atomic{Int}(0)
        localthreecopcount=Threads.Atomic{Int}(0)
        localfourcopcount=Threads.Atomic{Int}(0)

        liste=loadList(i,nbfiles,n)

        Threads.@threads for g in liste
            if oneCopWin(g)
                Threads.atomic_add!(localonecopcount,1)
            elseif twoCopWin(g)
                Threads.atomic_add!(localtwocopcount,1)
            elseif threeCopWin(g)
                Threads.atomic_add!(localthreecopcount,1)
                d3[string(i,"--",Threads.threadid(),"--",localthreecopcount[])]=g
            else
                Threads.atomic_add!(localfourcopcount,1)
                d4[string(i,"--",Threads.threadid(),"--",localfourcopcount[])]=g
            end
        end

        totalonecopcount=totalonecopcount+localonecopcount[]
        totaltwocopcount=totaltwocopcount+localtwocopcount[]
        totalthreecopcount=totalthreecopcount+localthreecopcount[]
        totalfourcopcount=totalfourcopcount+localfourcopcount[]


        println(string(i," ",localonecopcount[]," ",localtwocopcount[]," ",localthreecopcount[]," ",localfourcopcount[]," "))
        flush(stdout)
    end

        savegraph(string("./",n,"_3cops.g6"), d3, GraphIO.Graph6.Graph6Format())
        savegraph(string("./",n,"_4cops.g6"), d4, GraphIO.Graph6.Graph6Format())

    println(string("Total : ", totalonecopcount," ",totaltwocopcount," ",totalthreecopcount," ",totalfourcopcount," "))
end

# To start the program from the command line
fctThreaded(parse(Int64, ARGS[1]),parse(Int64, ARGS[2]))
