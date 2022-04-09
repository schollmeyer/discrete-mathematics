###
###
###

if(FALSE){


sample_shatterable_K_objset <- function(context,K,subset=rep(0,nrow(context))){
  if(sum(subset)==K){return(list(subset=subset))}
  extent <- operator_closure_obj_input(subset,context)
  idx <- which(extent==0)
  if(sum(subset)==0){
    new_subset <- subset
	new_subset[sample((1:nrow(context)),size=1)]=1
	
	return(sample_shatterable_K_objset(context,K,new_subset))
  }
	
  for(k in sample(idx)){
  #print(k)
    new_subset <- subset
    new_subset[k] <-1
    if(objset_is_shatterable(new_subset,context)){return(sample_shatterable_K_objset(context,K,new_subset))}
       
    }
    
    return(NULL)
    
}
       
 objset_is_shatterable <- function(subset,context){
   reduced_context <- context[which(subset==1),]
   reduced_context <- reduced_context[,which(colSums(reduced_context)==sum(subset)-1)]
                                     
 return(nrow(unique(t(reduced_context)))==sum(subset))}
 
 #is_ufg_generator <- function(subset,context,big_context){
 
 
 
 
 
 objset_is_ufg_candidate <- function(subset,context,big_context){
   if(!objset_is_shatterable(subset,context)){return(FALSE)}
   
   reduced_context <- context[which(subset==1),]
   #reduced_context <- reduced_context[,which(colSums(reduced_context)==sum(subset)-1)]
   
   mask= (colSums(reduced_context)==sum(subset)-1)
   
   for(k in (1:nrow(big_context))){
     t=0
     for(l in 1:nrow(reduced_context)){
        if(any(reduced_context[l,]==0 & big_context[k,]==0 & mask==1)){t=t+1} 
     }
	 if(t==nrow(reduced_context)){return(TRUE)}
   }
   
 return(FALSE)}
   
   
                                     
#  objset_is_ufg_candidate(E[1,],aa)
  
  
 


sample_shatterable_K_ufg_candidate <- function(context,big_context=context,K,subset=rep(0,nrow(context)),vector=NULL,number_ignored_vectors=0){
  if(sum(subset)==K){return(list(subset=subset,vector=vector))}
  extent <- operator_closure_obj_input(subset,context)
  idx <- which(extent==0)
  if(sum(subset)==0){
    new_subset <- subset
	new_subset[sample((1:nrow(context)),size=1)]=1
	
	return(sample_shatterable_K_ufg_candidate(context,big_context,K,new_subset,vector=which(new_subset==1)))
  }
	
number_ignored_vectors <- number_ignored_vectors + length(which(extent==1 & subset==0))
  for(k in sample(idx)){
  #print(k)
    new_subset <- subset
    new_subset[k] <-1
    if(objset_is_ufg_candidate(new_subset,context,big_context)){return(sample_shatterable_K_ufg_candidate(context,big_context,K,new_subset,vector=c(vector,k)))}
       
    }
    
    return(NULL)
    
}

#while(TRUE){e=NULL;while(is.null(e)){e=sample_shatterable_K_objset(aa,K=4);if(test_if_union_free_generator(e$subset,aa)){E=unique(rbind(E,e$subset));print(dim(E))}}}

test_if_union_free_generator <- function(subset,context){
  if(all(operator_closure_obj_input(subset,context)==subset)){return(FALSE)}
  if(test_if_generator(subset,context)==FALSE){return(FALSE)}
  extent <- operator_closure_obj_input(subset,context)
  j=NULL
  t=0
  for(k in which(extent==1)){
  t=0
    for(l in which(subset==1)){
    j=NULL

      for(i in (1:ncol(context))){
         if(context[l,i]==0 & sum(context[which(subset==1),i])==sum(subset)-1){j=c(j,i)}
      }


      if(any(context[k,j]==0)){t=t+1}
      }
      #print(c(t,sum(subset)))
      if(t==sum(subset)){return(TRUE)}
     }

return(FALSE)}


sample_shatterable_K_objset2 <- function(context,K){
  i<- sample(1:nrow(context))
  perm_context <- context[i,]
  A=extent.VC(perm_context)
  A$A=rbind(A$A,c(rep(1,nrow(context)),rep(0,ncol(context))))
  A$rhs=c(A$rhs,K)
  A$sense=c(A$sense,">=")
  A$obj=c(-((1:nrow(context))^0.5+CC*runif(nrow(context))),rep(0,ncol(context)))
  A <<- A
  B=gurobi(A)
  #B <<- B
  e<- rep(0,nrow(context))
  e[i]=(B$x[(1:nrow(context))])
return(e)}



sample_K_ufg_objset <- function(context,K){### smpled ufg-Prämisse der Kardinalität K, ACHTUNG: NICHT UNIFORM
  i<- sample(1:nrow(context))
  perm_context <- context[i,]
  A=ufg_dimension(perm_context)
  A$A=rbind(A$A,c(rep(1,nrow(context)),rep(0,ncol(context)),rep(0,nrow(context))))
  A$rhs=c(A$rhs,K)
  A$sense=c(A$sense,">=")
  A$obj=c(-((1:nrow(context))^0.5+CC*runif(nrow(context))),rep(0,ncol(context)),rep(0,nrow(context)))
  A <<- A
  B=gurobi(A,list(outputflag=0))
  #B <<- B
  e<- rep(0,nrow(context))
  e[i]=(B$x[(1:nrow(context))])
return(e)}



ufg_dimension <-function(X,additional.constraint=TRUE){  # Berechnet VC-Dimension eines Kontextes X
  m=dim(X)[1]
  n=dim(X)[2]
  ans=list()
  ans$A=array(0,c(2*(m+n)+ m +n   + m,m+n + m))
  ans$rhs=rep(0,2*(m+n)+m+n)
  ans$sense=rep("",2*(m+n))
  t=1
  for(i in (1:m)){
    j=which(X[i,]==0)     ## a)
    ans$A[t,j+m]=1
    ans$A[t,i]=n-1
    ans$rhs[t]=n
    ans$sense[t]="<="
    t=t+1
    
    ans$A[t,j+m]=1       ## b)
    ans$A[t,i]=-1
    ans$rhs[t]=0
    ans$sense[t]=">="
    t=t+1
  }
  
  
  
  for(j in (1:n)){
    i=which(X[,j]==0)     ## a)
    ans$A[t,i]=1
    ans$A[t,j+m]=m-1
    ans$rhs[t]=m
    ans$sense[t]="<="
    t=t+1
    
    ans$A[t,i]=1       ## b)
    ans$A[t,j+m]=-1
    ans$rhs[t]=0
    ans$sense[t]=">="
    t=t+1
  }
   
for(i in (1:m)){     ## Fuer ufg: Gegenstand b mit entsprechend Nullen muss existieren
   j=which(X[i,]==1)
   ans$A[t,j+m]=-1
   #ans$A[t,(1:m)]=-1
   ans$A[t,i+m+n]=-n
   ans$rhs[t]=-n
   ans$sense[t]=">="   
   t=t+1
}   

for(j in (1:n)){
	i <- which(X[,j]==0)
	ans$A[t,i+m+n] <- 1
		ans$A[t,i] <- -1 
		ans$rhs[t] <- 0
		ans$sense[t] <- "<="
		t <- t+1
		}
		
		
		
		for(i in (1:m)){
		ans$A[t,i]=1
		ans$A[t,i+m+n]=1
		ans$sense[t] ="<="
		ans$rhs[t]=1
		 t=t+1
		 }
		t <- t-1
		
		ans$A <- ans$A[(1:t),]
		ans$sense <- ans$sense[(1:t)]
		ans$rhs <- ans$rhs[(1:t)]
		
		



ans$modelsense="max"
ans$lb=rep(0,m+n+m)
ans$ub=rep(1,m+n+m)
ans$vtypes=c(rep("B",m),rep("B",n),rep("B",m))
ans$obj=c(rep(1,m),rep(0,n),rep(0,m))   

ans$A=rbind(ans$A,c(rep(1,m),rep(0,n),rep(0,m)),c(rep(0,m),rep(1,n),rep(0,m)),rep(1,m+n+m),c(rep(0,m+n),rep(1,m)))
ans$rhs=c(ans$rhs,min(m,n),min(m,n),n+m,1)
ans$sense=c(ans$sense,"<=","<=","<=",">=") 

if(additional.constraint){
  ans$A=rbind(ans$A,c(rep(-1,m),rep(1,n),rep(0,m)))
  ans$rhs=c(ans$rhs,0)
  ans$sense=c(ans$sense,"=")
  }
return(ans)}
	 

#e=NULL;while(is.null(e)){e=sample_shatterable_K_objset2(aa,K=5)}
	 #
objset_is_sufg_candidate <- function(subset,context,K){ #tests if subset is enlargable to a sufg premise of size K
A <- sufg_dimension(context)
A$lb[which(subset==1)] <-1
A$A <- rbind(A$A,c(rep(1,nrow(context)),rep(0,ncol(context)),rep(0,nrow(context))))
  A$rhs <- c(A$rhs,K)
  A$sense <- c(A$sense,"=")
  A$obj <- NULL
  B <- gurobi(A,list(outputflag=0))
return(B$status=="OPTIMAL")}


sample_ufg_K_objset_recursive <- function(context,K,subset=rep(0,nrow(context)),count=rep(0,K),p=1){
print(subset)
#print(count)
  #if(sum(subset)==K+1){return(list(subset=old_subset,pp=p,p=prod(count[(1:(K-1))])))}
  extent <- operator_closure_obj_input(subset,context)
  idx <- which(extent==0)
	#print(idx)
  if(sum(subset)==0){
	p=1/length(idx)
	print(p)
    new_subset <- subset
	new_subset[sample(idx,size=1)]=1
	
	return(sample_ufg_K_objset_recursive(context,K,new_subset,count,p))
  }
	
  idx2=NULL
  for(k in idx){
  #while(TRUE & sum(subset)!=0){
  #print(k)
  #k=sample(idx,size=1)
	 # if(sum(subset)>0){
	  count[sum(subset)]=count[sum(subset)]+1
	  
	  #print(count)
	  
	  
    new_subset <- subset
    new_subset[k] <-1
    if(objset_is_ufg_candidate(new_subset,context,K)){idx2=c(idx2,k)}
	#print(idx2)
  }
	print(idx)
	print(idx2)
	p=p*1/length(idx2)
	#print(sum(subset))
	print(p)
	
	new_subset <- subset
	new_subset[sample(idx2,size=1)]=1
	
	if(sum(subset)==K-1){
	  
	
	  return(list(subset=new_subset,pp=p,p=prod(count[(1:(K-1))])))
	 }
	
	
	return(sample_ufg_K_objset_recursive(context,K,new_subset,count,p))
	
	
	   
       
    
    
    #return(NULL)
    
}


sample_ufg_K_objset_recursive <- function(context,K){
p <-1 
Subset <- rep(0,nrow(context))
Vector=NULL
for(k in (1:(K))){
   
   counter <-1
   extent <- operator_closure_obj_input(Subset,context)
   print(c("extent",extent))
   idx <- which(extent==0)
   print(c("idx",idx))
   #counter=1
   #while(TRUE){
   idx2=NULL
   for(l in idx){
   
    
     #l <- sample(idx,size=1)
	 #print(c(l,"mm"))
	 new_subset <- Subset
	 new_subset[l] <- 1
	 if(objset_is_ufg_candidate(new_subset,context,K)){
	 idx2=c(idx2,l)
	 }
	 }
	 
	 print(c("idx2",idx2))
	 
	 p <- c(p,1/length(idx2))#/length(idx)#counter/length(idx)#1/counter
	 if(length(idx2)>1){print("a");	 l=sample(idx2,size=1)}# <- new_subset
	 else{print("b");l=idx2}
	 print(c("l",l))
	 Subset[l] <- 1
	 #print(Subset)
	 
	 Vector <- c(Vector,l)
	 print(l)
	 print(Vector)
	 
	 
    
   
     #break   
     #}
	 #else{counter <- counter + 1}
	#}
}

return(list(Subset = Subset, p=p,Vector=Vector))}

e=sample_ufg_K_objset_recursive(aa,K=3)





E=NULL;p=NULL

for(k in (1:1000000)){e=sample_ufg_K_objset_recursive(aa,K=3);E=rbind(E,e$Vector);p=rbind(p,e$p);print(c(dim(E),"#####################################################################"))}



#####
pp=rep(0,nrow(E))
for(k in (1:nrow(E))){pp[k]=prod(p[k,(1:4)])}
q=counts(E,pp)
q[,1]=q[,1]/nrow(E)
plot(q)
lines(q[,1],q[,1])

#####
#e=sample_ufg_K_objset2(aa,K=3)


 #for(k in (1:100000)){e=sample_K_ufg_objset2(aa,K=4);print(c(dim(E),"##########################"));E=rbind(E,e)}
 #D=rep(0,nrow(aa))
 #for(k in (1:nrow(E))){
 
 #D=D+operator_closure_obj_input(E[k,],aa)}
 
 
 #############
 
 
 #X=combinations(10,3)-1
 
 #E=array(0,c(nrow(X),10))
 #for(k in (1:nrow(X))){
 
 #e=rep(0,10)
 #e[X[k,]]=1
 #if(objset_is_ufg_candidate){D[k]=D[k]+1
 
 
}
 
 
################
################
################
################
################
################
################ KURIERTER TEIL

sufg_dimension <-function(X,additional.constraint=TRUE){  # Berechnet sufg-Dimension eines Kontextes X (s bezieht sich auf small i.S.v. der kleine Kontext ist der große Kontext
  m <- dim(X)[1]
  n <- dim(X)[2]
  ans <- list()
  ans$A <-array(0,c(2*(m+n)+ m +n   + m,m+n + m))
  ans$rhs <- rep(0,2*(m+n)+m+n)
  ans$sense <- rep("",2*(m+n))
  t <-1
  for(i in (1:m)){
    j <- which(X[i,]==0)     ## a)
    ans$A[t,j+m] <- 1
    ans$A[t,i] <- n-1
    ans$rhs[t] <- n
    ans$sense[t] <- "<="
    t <- t+1
    
    ans$A[t,j+m] <- 1       ## b)
    ans$A[t,i] <- -1
    ans$rhs[t] <- 0
    ans$sense[t] <- ">="
    t <- t+1
  }
  
  
  
  for(j in (1:n)){
    i <- which(X[,j]==0)     ## a)
    ans$A[t,i] <- 1
    ans$A[t,j+m] <- m-1
    ans$rhs[t] <- m
    ans$sense[t] <- "<="
    t <- t+1
    
    ans$A[t,i] <- 1       ## b)
    ans$A[t,j+m] <- -1
    ans$rhs[t] <- 0
    ans$sense[t] <- ">="
    t <- t+1
  }
   
for(i in (1:m)){     ## Fuer ufg: Gegenstand b mit entsprechend Nullen muss existieren
   j <- which(X[i,]==1)
   ans$A[t,j+m] <- -1
   ans$A[t,i+m+n] <- -n
   ans$rhs[t] <- -n
   ans$sense[t] <- ">="   
   t <- t+1
}   

for(j in (1:n)){
	i <- which(X[,j]==0)
	ans$A[t,i+m+n] <- 1
		ans$A[t,i] <- -1 
		ans$rhs[t] <- 0
		ans$sense[t] <- "<="
		t <- t+1
		}
		
		
		
		for(i in (1:m)){###  Objekt b aus Charakterisierung ufg darf nicht mit Gegenstand aus Kontranominalskala übereinstimmen (nur wichtig, wenn einelementige UFG betrachtet wird)
		ans$A[t,i] <- 1
		ans$A[t,i+m+n] <- 1
		ans$sense[t] <- "<="
		ans$rhs[t] <- 1
		 t <- t+1
		}
		t <- t-1
		
		ans$A <- ans$A[(1:t),]
		ans$sense <- ans$sense[(1:t)]
		ans$rhs <- ans$rhs[(1:t)]
		
		



ans$modelsense <- "max"
ans$lb <- rep(0,m+n+m)
ans$ub <- rep(1,m+n+m)
ans$vtypes <- c(rep("B",m),rep("B",n),rep("B",m))
ans$obj <- c(rep(1,m),rep(0,n),rep(0,m))   

ans$A <- rbind(ans$A,c(rep(1,m),rep(0,n),rep(0,m)),c(rep(0,m),rep(1,n),rep(0,m)),rep(1,m+n+m),c(rep(0,m+n),rep(1,m)))
ans$rhs <- c(ans$rhs,min(m,n),min(m,n),n+m,1)
ans$sense <- c(ans$sense,"<=","<=","<=",">=") 

if(additional.constraint){
  ans$A <- rbind(ans$A,c(rep(-1,m),rep(1,n),rep(0,m)))
  ans$rhs <- c(ans$rhs,0)
  ans$sense <-c(ans$sense,"=")
  }
return(ans)}


sample_sufg_K_objset_recursive_c <- function(context,K,N=rep(nrow(context),K),threads=1){
# Samples an ufg premise of size K
# Caution It is assumed that the large context is the given context 'context' therefore the name sufg (for small ufg)
# @context: Given context
# @K size of ufg premise
# @N vector for the number of random draws in every step (default value is nrow(context), which means that the drawing probability for a sampled ufg premise is exactly computed in this case. Otherwise (for smaller values) this probability is estimated ( in such a way that 1/p is estimated in an unbiased way )
# @threads: number of threads used by gurobi

#Return (vector): smpled premise set as an indicator vector ßin \{0,1\}^nrow(context)


	model <- sufg_dimension(context)  ## use MILP programe for checking if a given set Subset can be enlarged to a sufg-premise of size K
    model$A <- rbind(model$A,c(rep(1,nrow(context)),rep(0,ncol(context)),rep(0,nrow(context))))## Modification of model: demand that size of sufg-premise is at least K ('==K' would be also possible:  !!!Noch checken: Ist nicht eigtll. == erforderlich?
    model$rhs <- c(model$rhs,K)
    model$sense <- c(model$sense,">=")
    model$obj <- NULL## es soll nur getestet werden, ob Subset zu einer sufg-Prämisse der Größe >=K erweiterbar ist.

    NN <- N # unmber of draws in every step: will be modified during the sampling
    p_inverse <-1   # Vector of inverse probabilities of drawing in every step
    Subset <- rep(0,nrow(context))
    Vector=NULL   ## index Vector of the premise set
    idx3 <- NULL
	
    for(k in (1:(K))){
      counter <-1
      extent <- operator_closure_obj_input(Subset,context)
      idx <- which(extent==0)
      idx2=NULL
      NN[k]=min(N[k],length(idx))
      idx_sample <- sample(idx,size=NN[k])
      for(l in idx_sample){
   	     new_subset <- Subset
	     new_subset[l] <- 1
	     model$lb[which(new_subset==1)] <- 1
	     model$lb[which(new_subset==0)] <- 0
	     model$ub[idx3] <- 0
	     ans <- gurobi(model,list(outputflag=0,threads=threads))
	     if(ans$status=="OPTIMAL"){ idx2=c(idx2,l)}
	     else{idx3=c(idx3,l)}
	    }
	 
	Vector <- c(Vector,idx2[1])
	Subset[idx2[1]] <- 1	 
	p_inverse <- c(p_inverse,length(idx)*length(idx2)/NN[k])
	 
}

return(list(Subset = Subset, p_inverse=p_inverse,Vector=Vector))}



objset_is_sufg_candidate <- function(subset,context,K){ #tests if subset is enlargable to a sufg premise of size K
A <- sufg_dimension(context)
A$lb[which(subset==1)] <-1
A$A <- rbind(A$A,c(rep(1,nrow(context)),rep(0,ncol(context)),rep(0,nrow(context))))
  A$rhs <- c(A$rhs,K)
  A$sense <- c(A$sense,"=")
  A$obj <- NULL
  B <- gurobi(A,list(outputflag=0))
return(B$status=="OPTIMAL")}


ufg_sample_depth <- function(context,subset_sample,p_inverse){
   depth <- rep(0,nrow(context))
   for(k in (1:nrow(subset_sample))){
      extent <- operator_closure_obj_input(subset_sample[k,],context)
	  depth <- depth +extent*p_inverse[k]
	}

return(depth)}


for(k in (1:1000)){e=sample_sufg_K_objset_recursive_c(X,K=4,N=rep(4,4));E=rbind(E,e$Subset);p=c(p,prod(e$p_inverse));print(k)}




