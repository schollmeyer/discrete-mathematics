######


ranking_scaling <- function(X,C=0,remove.full.columns=TRUE){
  m=dim(X)[1]
  n=dim(X)[2]
  NAMES=rep("",n^2)
  ans=array(0,c(m,n^2))
  temp=array(0,c(n,n))
  for(k in (1:m)){
    for(l1 in (1:n)){
      for(l2 in (1:n)){
        temp[l1,l2]=((X[k,l1]  <= X[k,l2])  & (X[k,l1] +C >= X[k,l2]) )*1
      }
    }
    ans[k,]=as.vector(temp)
  }
  t=1
  for(l1 in (1:n)){
    for(l2 in (1:n)){
      NAMES[t]=paste(c(colnames(X)[l1]," <= ",colnames(X)[l2], "; C=",C),collapse="")
      t=t+1
    }
  }
  colnames(ans)=NAMES
  if(remove.full.columns){
    i=which(colSums(ans)==m)
    ans=ans[,-i]
  }
  return(ans)}






####
#### Einigermaßen kuratierter Teil (aber noch unkommentiert (sagte der Barbier von Sevilla))


is_strictly_K_concave <- function(depth_values,context,K,nrep=10000){
  for(k in (1:nrep)){
    size <- sample((2:K),size=1)
    i <- sample((1:nrow(context)),size=size)
    temp <- rep(0,nrow(context));temp[i] <- 1
    temp2 <- operator_closure_obj_input(temp,context)
    j <- which(temp2==1 & temp==0)
    if(length(j)>0){
      A <- min(depth_values[setdiff(i,j)])
      B <- min(depth_values[j])
      if(A>=B){return(list(ans=FALSE,counterexample_premise=setdiff(i,j),counterexample_conclusion=j[which.min(depth_values[j])]))}
    }
  }
  
return(list(ans=TRUE,counterexample_premise=NULL,counterexample_conclusion=NULL))}


is_K_concave <- function(depth_values,context,K,nrep=10000){
  for(k in (1:nrep)){
    size <- sample((2:K),size=1)
    i <- sample((1:nrow(context)),size=size)
    temp <- rep(0,nrow(context));temp[i] <- 1
    temp2 <- operator_closure_obj_input(temp,context)
    j <- which(temp2==1 & temp==0)
    if(length(j)>0 & any(temp2==0)){
      A <- min(depth_values[setdiff(i,j)])
      B <- min(depth_values[j])
      if(A>B){return(list(ans=FALSE,counterexample_premise=setdiff(i,j),counterexample_conclusion=j[which.min(depth_values[j])]))}
    }
  }
  
  return(list(ans=TRUE,counterexample_premise=NULL,counterexample_conclusion=NULL))}







all_quasiorders <- function(number_obj){
  indexs <- which(diag(number_obj) ==0)
  
  quickhull <- function(subset_attributes,context){
    I <- diag(number_obj)
    I[indexs] <- subset_attributes
    I <- relation_incidence(transitive_closure(as.relation(I)))
    return(as.vector(I[indexs]) )                       
    
  }
  
  
  ans <- compute_all_closure(quickhull,context=diag(number_obj^2-number_obj))
  return(ans)
  
}

all_partial_orders <- function(K,names=(1:K)){
  
  X <- permutations(K,K)
  colnames(X) <- names
  m <- nrow(X)
  
  context <- ranking_scaling(X,C=K,TRUE)
  ans <- calculate_concept_lattice(context=context,compute_extents=FALSE)
  ans <- ans$intents[-nrow(ans$intents),]
  colnames(ans) <- colnames(context)
  return(ans)
  
  
}


vec_to_incidence <- function(vec){
  
  number_obj <- sqrt(length(vec)+1/4) +1/2
  
  I <- diag(number_obj)
  indexs <- which(I==0)
  I[indexs] <- vec
return(I)}


encl <- function(subset_objects, context){
  m <- nrow(context)
  n <- ncol(context)
  ans <- rep(Inf,m)
  for(k in (1:m)){
   extent <- rep(0,m);extent[k] <- 1
   extent <-operator_closure_obj_input(extent,context) 
   if(all(extent>= subset_objects) & any(extent > subset_objects)){ans[k]<- sum(extent)}
  }
  k <-which(ans==min(ans))
  print(which(ans==min(ans)))
  extent <- rep(0,m);extent[k] <- 1
  extent <-operator_closure_obj_input(extent,context) 
  return(extent)
  
  
}                
 

shortest_path_dist <- function(incidence_mat){
  
  m <- nrow(incidence_mat)
  ans <- array(Inf,c(m,m))
  mat <- relation_incidence(transitive_reduction(as.relation(incidence_mat)))
  for(k in (1:m)){
    i <- which(mat==1)
    ans[i] <- pmin(ans[i],(array(k,c(m,m)))[i])
    mat <- compute_relation_product(mat,mat)
    
  }
  
return(ans)  
}  

skew_pseudometric1 <- function(departure, destination){
  if(length(which(destination==0 & departure==1))==0){return(0)}
  return(max((shortest_path_dist(departure))[which(destination==0 & departure==1)]))
  
}

skew_pseudometric2 <- function(departure, destination){
  if(length(which(departure==0 & destination==1))==0){return(0)}
  ans <- 0
  M <- shortest_path_dist(destination)
  for(k in which(departure==0 & destination==1)){
    temp <- departure;temp[k]=1;temp <-compute_transitive_hull(temp)
    #print(temp)
     mat <- shortest_path_dist(temp)
     print((abs((mat-M)[which(temp==1)])))
     ans <- max(ans, max(abs((mat-M)[which(temp==1)])))
    
    
  }
  return(ans)}

skew_metric <- function(departure,destination){
  return(max(skew_pseudometric1(departure,destination),skew_pseudometric1(departure,destination)))
}

  


#skew_metric(vec_to_incidence(ans[2,]),vec_to_incidence(ans[20,]))
  #operator_closure_obj_input(e,a)


#####



# #Tukeys_depth=function(X){  ### FRAGWUERDIG berechnet Levelfunktion fuer begriffliches Quantilkonzept
#   n=dim(X)[1]
#   
#   A=colMeans(X)
#   
#   l=rep(0,n)
#   for(k in (1:n)){
#     temp=X[k,]
#     l[k]=min(A[which(temp==1)])
#   }
#   return(l)}
# 
Tukeys_outlyingness <- function(context,weights=rep(1,nrow(context))){  ### berechnet Levelfunktion fuer begriffliches Quantilkonzept
  n <- nrow(context)
  m <- ncol(context)
  A <- rep(0,m)
  for(k in (1:m)){
    A[k] <- mean(context[,k]*weights)}
    l <- rep(0,n)

  for(k in (1:n)){
    temp <- context[k,]
    l[k] <- max(A[which(temp==0)])
  }

return(l)}

Tukeys_depth <- function(context,weights=rep(1,nrow(context))){1-Tukeys_outlyingness(context,weights)}

nu_min <- function(E,context,...){
  
  m <- sum(E)
  if(m==1){return(which(E==1))}
  if(m==1 | all(colSums(context[which(E==1),]) %in% c(0,m))){return(which(E==1)[1])}
  I <- calculate_psi(E,context)
  ans <- min_k_obj_generated(E,I,context)
  bns <- gurobi(ans,...)
  return(which(bns$x[-(1:ncol(context))]==1))}

nu_closed <- function(E,context){
  m <- sum(E)
  if(m==1){return(which(E==1))}
  if(m==1 | all(colSums(context[which(E==1),]) %in% c(0,m))){return(which(E==1)[1])}
    extr <- extreme_points(context)
    ans <- rep(0,nrow(context))
    ans[which(extr==1)] <- 1
    extr <- operator_closure_obj_input(extr,context)
    ans[which(E==1 & extr==0)] <- 1
  return(ans)}
    
  
  
  
  




peeling_depth <- function(context,peeling_operator=nu_min,...){
  m <- nrow(context)
  ans <- rep(0,m)
  idx <- (1:m)
  k <- 1
  context2 <- context
  while(TRUE){
    i <- peeling_operator(rep(1,nrow(context2)),context2,...)
    if(length(i)==0){return(ans)}
    #print(idx)
    #print(i)
    ans[idx[i]] <- k
    idx <- idx[-i]
    if(length(idx)==0){return(ans)}
    k <- k+1
    
    context2 <- matrix(context2[-i,],nrow=dim(context2)[1]-length(i))
    
  }
}


quasiconcave_hull <- function(depth_values,context){
  ans <- rep(0,length(depth_values))
  for(k in sort(unique(depth_values))){
    i <- which(depth_values>=k)
    temp <- rep(0,nrow(context))
    temp[i] <- 1
    temp <- operator_closure_obj_input(temp,context)
    ans[which(temp==1)] <- k
    
  }
return(ans)  
}



minimal_extent <- function(object_subset,context,...){
  # computes minimal (w.r.t. cardinality (and therefore also w.r.t. set-inclusion))
  # extent that is a superset of the given set object_subset (given as indicator vector)
  m <- length(object_subset)
  model <- min_k_objextent_opt_b(context,(1:m),rep(1,m))
  model$modelsense <- "min"
  model$lb[which(object_subset==1)]=1
  ans <- gurobi(model,...)
  
  return(ans$x[(1:m)])
  
}

## test:
#set.seed(1234567)
#X <- rnorm(25*2);dim(X) <-c(25,2)
#plot(X)
#points(X[c(1,1),],col="red")
#I <- convex.incidence(X)
#temp <- rep(0,25)
#temp[1] <- 1
#ans <- minimal_extent(temp,I$context)


#### noch zu checken:
peeled_nu_min=function(E,context,K=1,VC=Inf){
  i <-NULL
  j <- NULL
  for(k in (1:K)){
    print(i)
    print(j)
    
    #E <<- E
    if(is.null(j) | length(j)==dim(context)[2]){i <- nu_min(E,context)}
    else{i <- nu_min(E,context[,-j])}
    if(length(i)<=VC){return(i)}
    j <- c(j, which(colSums(matrix(context[i,],nrow=length(i)))==length(i)-1))
    print("j")
    print(j)
  }
  return(i)}





plot_contours <- function(X,D,...){
  Dsort <- sort(unique(D))
  m <- length(Dsort)
  plot(X,...)
  for(k in (1:m)){
    i <- which(D>=Dsort[k])
    j <- chull(X[i,])
    lines(X[i[c(j,j)],])
  }
}

plot_non_closed_contours <- function(X,D,...){
  Dsort <- sort(unique(D))
  m <- length(Dsort)
  plot(X,...)
  for(k in (1:m)){
    i <- which(D>=Dsort[k])
    
    j <- chull(X[i,])
    lines(X[i[c(j,j)],],...)
    
  }
}





min_k_attr_generated <- function(extent,intent,context){  # Berecchnet für Begriff gegeben durch Umfang extent und Inhalt intent das maximale k, für das der Begriff k-Merkmalserzeugt ist (Kontext X muss ebenfalls mit übergeben werden)
  m=nrow(context)
  n=ncol(context)
  model=k_extent_opt_b(context,(1:m),(1:m),K=ncol(context))
  model$lb[which(extent==1)]=1
  model$ub[which(extent==0)]=0
  model$ub[which(intent==0)+m]=0
  model$obj=c(rep(0,m),rep(1,n))
  model$modelsense="min"
  return(model)}


min_k_obj_generated <-function(extent,intent,context){min_k_attr_generated(intent,extent,t(context))}

####
#### Ende Einigermaßen kuratierter Teil


k_extent_opt_b <-function(X,gen.index,v,binary.variables="afap",K){##  extentopt: Version, wie TR 209, S.23 beschrieben, nur Ungleichungen (21) verschärft
  # berechnet Model zur Optimierun von Zielfunktion v über alle K-Merkmalserzeugte Begriffe
  m=dim(X)[1]
  n=dim(X)[2]
  mask=rep(0,m)
  mask[gen.index]=1
  N=2*(m+n)
  
  A= array(0,c(N,m+n))
  rhs=rep(0,N)
  sense=rep("",N)
  t=1
  for(k in (1:m)){         
    i=which(X[k,]==0)
    if(length(i)>=1){
      A[t,k]=length(i);A[t,i+m]=1;rhs[t]=length(i);sense[t]="<="
      t=t+1
    }
    
  }
  
  for(k in (1:n)){        
    i=which(X[,k]==0)
    if(length(i)>=1){
      A[t,k+m]=length(i);A[t,i]=1;rhs[t]=length(i);sense[t]="<="
      t=t+1
    }
    
  }
  
  for(k in (1:m)){
    i=which(X[k,]==0)
    if(length(i)>=1){
      A[t,which(X[k,]==0)+m]=1;A[t,k]=1;rhs[t]=1;sense[t]=">=";t=t+1
    }}
  
  # for(k in (1:n)){
  #j=which(mask==1 & X[,k]==0)
  #if(length(j)>=1){
  #A[t,which(mask==1 & X[,k]==0)]=1;A[t,k+m]=1;sense[t]=">=";rhs[t]=1;t=t+1}}
  t=t-1
  
  
  
  
  
  lb=rep(0,m+n)
  ub= rep(1,m+n)
  idx=which(colSums(X[gen.index,])==length(gen.index))
  if(length(idx)>0){lb[m+idx]=1}
  
  idx=which(rowSums(X[,])==n)
  if(length(idx)>0){lb[idx]=1}
  
  ###  setze je nach Methode gewisse Variablen als binaer
  vtypes=rep("C",m+n)
  if(binary.variables=="afap"){
    if(length(gen.index)<=min(m,n)){
      vtypes[gen.index]="B"
    }
    if(length(gen.index)>min(m,n) & m<=n){
      vtypes[(1:m)]="B"
    }
    if(length(gen.index)>min(m,n) & n<=m){
      vtypes[-(1:m)]="B"
    }
  }	
  
  if(binary.variables=="sd"){
    if(m<=n){
      vtypes[(1:m)]="B"
    }
    else{vtypes[-(1:m)]="B"}
  }
  
  if(binary.variables=="allgen"){
    vtypes[gen.index]="B"
    vtypes[-(1:m)]="B"
  }
  
  if(binary.variables=="all"){
    vtypes=rep("B",m+n)
  }
  
  if(  !(binary.variables %in% c("afap","sd","allgen","all"))){print("invalid argument for binary.variabes")}
  
  A=rbind(A[(1:t),],c(rep(0,m),rep(1,n)))
  rhs=c(rhs[(1:t)],K)
  sense=c(sense[(1:t)],"<")
  ##Über vtypes nochmalnachdenken:
  
  vtypes[(1:m)]="C"
  vtypes[-(1:m)]="B"
  
  return(list(A=as.simple_triplet_matrix(A),rhs=rhs,sense=sense,modelsense="max",lb=lb,ub=ub,obj=c(v,rep(0,n)),ext.obj=v,intent.obj=rep(0,n),m=m,n=n,vtypes=vtypes,n.constr=t,context=X))}


#Methode nicht 'idempotent', bezug zu population

#Focusing property

#sampling: double sampling
if(FALSE){
rm(list=ls())

library(gtools)
library(relations)

######
######
# Illustration Tiefenfunktionen

x <- matrix(sort(c((1:74),rep(75,200)+rnorm(200,sd=0.01),(76:100))),ncol=1)
context <- conceptual.scaling(x)
par(cex=1)

T <- 1- Tukeys_outlyingness(context)
plot(x,T/max(T),type="l")
P <- peeling_depth(context)


lines(x,P/max(P),type="l",col="red")
plot()
all_partial_orders <- function(K){
  KK <- K^2
 sets <- permutations(2,KK,repeats.allowed=TRUE)-1
 ans <- NULL
 for(k in (1:nrow(sets))){
     
     temp <- sets[k,]
     dim(temp) <- c(K,K)
     if(relation_is_partial_order(as.relation(temp))){
        
        ans=rbind(ans,as.vector(temp))}
     }
     
     
return(ans)}


all_quasiorders <- function(K){
  KK <- K^2
 sets <- permutations(2,KK,repeats.allowed=TRUE)-1
 ans <- NULL
 for(k in (1:nrow(sets))){
     
     temp <- sets[k,]
     dim(temp) <- c(K,K)
     if(relation_is_quasiorder(as.relation(temp))){
        
        ans=rbind(ans,as.vector(temp))}
     }
     
     
return(ans)}
                               
                               
betweenness <- function(P,Q,R){all(pmin(P,R)<= Q)}
tau_s <- function(P,Q){sum(pmax(P,Q))-sum(pmin(P,Q))}                             
                               

K <- 5							   
#RR <- all_partial_orders(K)
kk=0
set.seed(1234567891)
kk=kk+1
for(k in (1:1000000)){
I <- sample((1:nrow(RR)),size=3)
I <- sample((1:nrow(RR)),size=3)
P <- RR[I[1],]
Q <- RR[I[2],]
R <- RR[I[3],]

if(betweenness(P,Q,R) & !betweenness(P,R,Q) & tau_s(P,Q)>tau_s(P,R) &sum(pmin(P,R))>=7){break}
}

dim(P)=c(K,K)
dim(Q)=c(K,K)
dim(R)=c(K,K)

par(mfrow=c(1,3),bg="white")
plot(as.relation(P),main="P")
plot(as.relation(Q),main="Q")
plot(as.relation(R),main="R")
#####

#Beispiel Christoph
# Sind bucket orders? glaube nicht ganz)

P1 <- upper.tri(diag(5))
diag(P1) <- 1
P2 <- P1;P2[1,2] <- 0;P2[2,1] <- 1

P3 <- diag(5);P3[1,2] <- 1
P4 <- diag(5);P4[2,1] <- 1
tau_s(P1,P2)
tau_s(P3,P4)
par(mfrow=c(1,4),bg="white")
plot(as.relation(P1))
plot(as.relation(P2))
plot(as.relation(P3))
plot(as.relation(P4))

####

#weiterer Versuch
par(mfrow=c(1,1),bg="white")
set.seed(1234567)
P1=array(rnorm(25)>=0,c(5,5));diag(P1)=1;P1=transitive_closure(as.relation(P1))
plot(as.relation(P1))
###
K <- 4
for(k in (1:1000)){
  
  I=sample((1:nrow(RR)),size=4)
  P=RR[I[1],];dim(P)=c(K,K)
  Q=RR[I[2],];dim(Q)=c(K,K)
  R=RR[I[3],];dim(R)=c(K,K)
  S=RR[I[4],];dim(S)=c(K,K)
  P2=relation_incidence(transitive_reduction(as.relation(P)))
  Q2=relation_incidence(transitive_reduction(as.relation(Q)))
  
  R2=relation_incidence(transitive_reduction(as.relation(R)))
  S2=relation_incidence(transitive_reduction(as.relation(S)))
  if(tau_s(P,Q)==tau_s(R,S)  &  tau_s(P2,Q2)!=tau_s(R2,S2) ){break}
  
  
  
}

par(mfrow=c(1,4),bg="white")
plot(as.relation(P))
plot(as.relation(Q))
plot(as.relation(R))
plot(as.relation(S))






########

#Illustration metrischer Ansatz
nrep <- 1000
dat <- NULL
mu <- ans[1000000,]
lambda <- .02
while(TRUE){
  i <- sample((1:nrow(ans)),size = 1)
  dist <- tau_s(mu,ans[i,])
  if( runif(1) <=exp(-lambda*dist)){dat <- rbind(dat,ans[i,])}
  if(!is.null(dat)){if(nrow(dat) >= nrep){break}}
   
  
}

D <- array(0,c(nrep,nrep))
for(k in (1:nrep)){
  for(l in (1:nrep)){
    D[k,l] <- tau_s(dat[k,],dat[l,])

  }
}

library(MASS)
plot(sammon(D)$points)

points(sammon(D)$points,col="red")
}
