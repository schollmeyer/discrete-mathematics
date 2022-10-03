

library(Matrix)
library(gurobi)
library(igraph)  
library(Biobase) ##für Funktion rowMin
library(geometry) ## für Fufnktion cart2bar (für Erstellung Kontext für Geometrie)



source("statistical_models_for_partial_rankings.R",local=TRUE)
source("fca_implications_general.R",local=TRUE)
source("fca_ufg_partial_order.R",local=TRUE)



###################################
###################################
###### Convertion of Data Structures


list_to_context <- function(list){        #### converts a list of orders given by incidence relations as 0-1 matrices into a context of crosses
	m <- length(list)
	mat <- array(0,c(m, length(list[[1]])))
        
	for(k in (1:m)){
		mat[k,] <- as.vector(list[[k]])
	}
return(mat)				     
	
}
context_to_list <- function(context){
	m <- nrow(context)
	q <- sqrt(ncol(context))
	for(k in (1:q)){NAMES[k] <- colnames(context[1,k])}
	list <- list()
	for(k in (1:m)){
		temp <- context[k,];dim(k) <- c(q,q)
		colnames(temp) <- rownames(temp) <- NAMES
		list[[k]] <- temp
	}
				     
return(list)}
###################################
########				   ########
#######						#######
######     order theory  ######
#######                     #######
########				   ########
###################################

incidence=function(X){          ## erzeugt Inzidenzmatrix einer gegebenen Datentabelle (Zeilen entsprechen statistischen Einheiten und Spalten entsprechen Auspraegungen verschiedener Dimensionen. statistische Einheit x ist kleinergleich statistische Einheit y iff x_i <= y_i fuer jede Dimension i)
   m=dim(X)[1]
   ans=matrix(FALSE,ncol=m,nrow=m)
   for(k in (1:m)){
      for(l in (1:m)){
        ans[k,l]=all(X[k,]<=X[l,])
      }
   }
return(ans)}




relational_product=function(X,Y){  ### berechnet Relationenprodukt von X und Y : X;Y:= (p,q) : exists r: pXr und rYq,  vgl. z.B. http://www.math.tu-dresden.de/~ganter/inf2005/folien/Relationenslides.pdf
  m=dim(X)[1]
  n=dim(X)[2]
  o=dim(Y)[2]
  ans=array(0,c(m,o))
  if(dim(Y)[1]!=n){print("dimension missmatch!");stop}
  for(k in (1:n)){
    ans[which(X[,k]==1),which(Y[k,]==1)]=1
  }
return(ans)}




neighbour_incidence=function(I){     #berechnet Nachbarschaftsrelation (covering relation) zu einer homogenen Relation I)
  n=dim(I)[1]
  II=as.logical(I-relational.product(I-diag(rep(1,n)),I-diag(rep(1,n))))
  dim(II)=c(n,n)
return(II)}





transitive_hull=function(I){   #  berechnet transitive Huelle einer homogenen Relation  
  m=dim(I)[1]
  temp.old=array(0,c(m,m))
  temp=I
  while(any(temp.old!=temp)) {
    temp.old=temp
    temp=relational.product(temp,temp)
  }
return(temp)}

trr=function(I){        # Hilfsfunktion zur Funktion tr, siehe unten
  I1=I*lower.tri(I)
  I2=I*upper.tri(I)
  ans=pmax(neighbour_incidence(I1),neighbour_incidence(I2))
return(ans)}


tr=function(I){   # berechnet eine transitive (pseudo-)Reduktion einer Relation I (Ergebnis ist nicht notwendig minimal bezueglich Mengeninklusion und damit keine eigentliche transitive reduktion, vgl. auch https://en.wikipedia.org/wiki/Transitive_reduction
  o=order(colSums(I))
  ans=trr(I[o,o])
  p=invPerm(o)
return(ans[p,p])}



width.hopcroft.karp=function(II){  ## berechnet Weite einer geordneten Menge über eine  maximume Matching in einem bipartiten Graph formulierung und den Hopcroft-Karp Algorithmus

## siehe https://mathoverflow.net/questions/189161/fastest-algorithm-to-compute-the-width-of-a-poset
  if(is.null(II)){return(list(width=0))}
  n=dim(II)[1]
  I=transitive_hull(II)
  if(n==0){return(list(width=0))}
  II=I
  diag(II)=0
  II=rbind(cbind(0*II,II),cbind(0*II,0*II))
  G=graph_from_adjacency_matrix(II)
  V(G)$type <- c(rep(FALSE,n),rep(TRUE,n))
  ans=max_bipartite_match(G)
  print(n-ans$matching_size)
  return(list(width=n-ans$matching_size ))}
  
  
width=function(I){width.hopcroft.karp(I)$width} #Berechnet Weite einer geordneten Menge ueber die Funktion width.hopcroft.karp


downarrow=function(x,bg){ # berechnet Menge aller Elemente unterhalb einer gegebenen Menge M (gegeben durch x[i]=1 iff i \in M)  (bezueglich der Relation bg$incidence) 
  if(all(x==0)){return(x)}  
  else{
    index=which(x==1)
    temp=bg$incidence[,index]
    dim(temp)=c(length(temp)/length(index),length(index))
    i=which(rowSums(temp)>=1)
    ans=x
    ans[i]=1
    return(ans)
  }
}




##########################################
########			     	      ########
#######						       #######
######     Fomal Concept Analysis    ######
#######                            #######
########				          ########
##########################################

next_closure=function(cop,context,stepsize,n=dim(context)[2],Nmax=700000){   # Next closure Algorithmus zur Berechnung aller Huellen eines gegebenen Hüllenoperators cop vgl. z.B. Ganter. Diskrete Mathematik: geordnete Mengen S.86
  A=rep(0,n)
  A=cop(A,context)
  ans=array(as.logical(0),c(Nmax,n))
  ans[1,]=A
  t=2
  while(TRUE){
    supp=which(A==1)
    if(length(supp)==0){index=(1:n)}
    else{index= (1:n)[-supp]}
    for(k in (sort(index,decreasing=TRUE))){
      temp=oplus(A,k,cop,context)
      if(lower.i(A,temp,k)){break}
     }
  A=temp
  ans[t,]=temp
  cond.print(t,step=t,stepsize=stepsize)
  t=t+1
  if(all(temp==1)){return(ans[(1:(t-1)),])}
  if(t>Nmax){ans=rbind(ans,array(as.logical(0),c(Nmax,n)));Nmax=2*Nmax}
 }
return(ans[(1:(t-1)),])  
} 


lower.i=function(A,B,i){  ### Hilfsfunktion fuer Next closure Algorithmus
  if(i==1){
    return(B[i]==1 & A[i]==0)
  }
  else{
   temp=rep(0,length(A));temp[(1:(i-1))]=1;return(B[i]==1 & A[i]==0 &all(pmin(A,temp)==pmin(B,temp)))}
}


plus=function(A,i){    ## Hilfsfunktion fuer Funktion oplus
  if(i==1){ans=rep(0,length(A));ans[i]=1;return(ans)}
  else{
    temp=rep(0,length(A));temp[(1:(i-1))]=1; ans=pmin(A,temp);ans[i]=1;return(ans)
  }
}

oplus=function(A,i,cop,bg){cop(plus(A,i),context)}  ## Hilfsfunktion fuer Next closure Algorithmus



PHI=function(A,context){  ##  Ableitungsoperator Phi
  i=which(A==1)
  temp=as.matrix(context[,i])
  dim(temp)=c(dim(context)[1],length(i))
  S=rowSums(temp)
  j=which(S==length(i))
  ans=rep(0,dim(context)[1])
  ans[j]=1
return(ans)}

PSI=function(B,context){    ## Ableitungsoperator Psi
  i=which(B==1)
  temp=as.matrix(context[i,])
  dim(temp)=c(length(i),dim(context)[2])
  S=colSums(temp)
  j=which(S==length(i))
  ans=rep(0,dim(context)[2])
  ans[j]=1
return(ans)}


L=function(A,context){   ## Operator L vgl. Ganter, Wille 1996 S. 80 ff
   temp=A
   if(all(A==0)){temp=H.attr(A,context)}
   else{
     index=which(A==1)
     for(k in index){
       temp2=A;temp2[k]=0
       
       temp=pmax(temp,H.attr(temp2,context))
     }
   }
   return(temp)
}

L.infty=function(A,context){   ## Operator L_infty vgl. Ganter, Wille 1996 S. 85 ff
   
   temp.old=A
   temp=L(A,context)
   while(any(temp.old!=temp)){
      temp.old=temp
      temp=L(temp,context)
   } 
return(temp)}

H.attr=function(A,context){PSI(PHI(A,context),context)} ## Berechnet zu Merkmalsmenge A (gegeben durch A[i]=1 iff Merkmal i ist in Menge A, 0 sonst) deren Hülle PSI(PHI(A))
	H.obj=function(A,context){PHI(PSI(A,context),context)} ## Berechnet zu Gegenstandsmenge A (gegeben durch A[i]=1 iff Gegenstand i ist in Menge A, 0 sonst) deren Hülle PHI(PSI(A))
	
implications=function(bg){               ### Hier stimmt was nicht!!!
  a=next_closure(L.infty,bg)
  print((a))
  CS=colSums(bg$context)
  i=which(CS==dim(bg$context)[1] )
  #a[,i]=0
  n=dim(a)[1]
  ans=list()
  ans$premise=NULL
  ans$conclusion=NULL
  for(k in (1:n)){
    temp=H.attr(a[k,],bg)
    if(any(a[k,]!=temp )){
       ans$premise=rbind(ans$premise,a[k,])
       ans$conclusion=rbind(ans$conclusion,temp-a[k,])
    }
  }
return(ans)}




concept_lattice=function(context,compute.extents=TRUE,stepsize=20000){### Berechnet Begriffsverband zu Kontext.
																		### stepsize beeinflusst nur die Anzeige des Berechnungsfortschritts: Pro  stepsize erzeugter Begriffe wird einmal ausgegeben, wieviele Begriffe bereits berechnet wurden
   
   ans=list()
   ans$intents=next_closure(H.attr,context,stepsize=stepsize)
   m=dim(ans$intents)[1]
   n=dim(context)[1]
   ans$concepts=rep("",m)
   if(compute.extents){ ans$extents=matrix(FALSE,nc=n,nr=m)
      for(k in (1:m)){
        ans$extents[k,]=PHI(ans$intents[k,],context)
        ans$concepts[k]=paste("{",paste((rownames(context))[which(ans$extents[k,]==1)],collapse=","),"}   {",paste((colnames(context))[which(ans$intents[k,]==1)] ,collapse=","),"}",collapse="")
      }
      
   }
   else{
     for(k in (1:m)){
        ans$concepts[k]=paste("{",paste((colnames(context))[which(ans$intents[k,]==1)],collapse=","),"}",collapse="")
     }
   }
   
   
   
   
   
return(ans)}




random_context=function(nrow=20,ncol=10,prob=0.5){matrix(runif(nrow*ncol)<=prob,nrow=nrow,ncol=ncol)*1}  ### Funktion erzeugt zufälligen Kontext



##########################################
########			     	      ########
#######						       #######
######     Conceptual Scaling   ######
#######                            #######
########				          ########
##########################################


col_reduce=function(X){  ## reduziert Kontext um reduzible Merkmale
  ans=NULL
  m=dim(X)[1]
  n=dim(X)[2]
  for(k in (1:n)){
    T=rep(0,n)
    T[k]=1
    TT=H_attr(T,context=X)
    TT[k]=0
    U1=PHI(TT,bg=list(context=X))
    if(any(U1!=X[,k])){ans=c(ans,k)}
  }
return(X[,ans])}


col.clarify=function(X){ t(unique(t(X)))}  ## reduziert einen Kontext um doppelte Spalten

remove.full.cols=function(X){  ## entfernt aus einem Kontext Spalten, die nur aus Kreuzen bestehen
  m=dim(X)[1]
  CS=colSums(X)
return(X[,which(CS!=m)])}

remove.full.rows=function(X){ ## entfernt aus einem Kontext Zeilen, die nur aus Kreuzen bestehen
  n=dim(X)[2]
  CS=colSums(X)
  RS=rowSums(X)
return(X[,which(RS!=n)])}



conceptual.scaling=function(X){  ## Hauptfunktion zum automatischen begrifflichen Skalieren
   N=dim(X)[1]
   m=dim(X)[1]
   n=dim(X)[2]
   D=conceptual.scaling.dim(X)
   XX=array(0,c(m,D$dim))
   CN=colnames(X)
   CN2=rep("",D$dim)
  
   
   t=1
   for(k in (1:n)){
      print(c(k,": ",class(X[,k])),quote=FALSE)
     if(class(X[,k])[1]=="ordered" | class(X[,k])[1]=="numeric" | class(X[,k])[1]=="integer"){ temp= cbind(ordinal.scaling.vec(as.numeric(X[,k]),CN[k]), dordinal.scaling.vec(as.numeric(X[,k]),CN[k]));XX[,(t:(t+D$K[k]-1))]=temp; CN2[(t:(t+D$K[k]-1))] <- colnames(temp);t=t+D$K[k]}
	 if(class(X[,k])[1]=="factor"){temp=1-nominal.scaling.vec(as.numeric(X[,k]),CN[k]) ; XX[,(t:(t+D$K[k]-1))]=temp;CN2[(t:(t+D$K[k]-1))]  =colnames(temp);t=t+D$K[k]}#,1-nominal.scaling.vec(as.numeric(X[,k])) )}
  } 
  
  colnames(XX)=CN2
return(XX)}  











ordinal.scaling.vec=function(x,add=NULL){  ## Funktion zur ordinalen Skalierung eines Vektors
  attr=sort(unique(x))
  m=length(attr)
  n=length(x)
  ans=array(0,c(n,m))
  NAMES=rep("",m)
  t=1
  for(k in (1:m)){
        NAMES[k]=paste(c(add," x<=", attr[k]),collapse="")
        ans[,k]=(x<=attr[k]  )

  }
colnames(ans)=NAMES
return(ans)}

ordinal.scaling=function(X){ ## Funktion zur ordinalen Skalierung einer Datenmatrix
  m=dim(X)[2]
  ans=NULL
  for(k in (1:m)){
     ans=cbind(ans,ordinal.scaling.vec(X[,k], add=c(colnames(X)[k],":")))
  }
return(ans)}




nominal.scaling.vec=function(x,add=NULL){  ## Funktion zur nominalen Skalierung eines Vektors
  attr=sort(unique(x))
  m=length(attr)
  n=length(x)
  ans=array(0,c(n,m))
  NAMES=rep("",m)
  t=1
  for(k in (1:m)){
        NAMES[k]=paste(c(add," ", attr[k]),collapse="")
        ans[,k]=(x==attr[k]  )

  }
colnames(ans)=NAMES
return(ans)}







nominal.scaling=function(X){ ## Funktion zur nominalen Skalierung einer datenmatrix
  m=dim(X)[2]
  ans=NULL
  for(k in (1:m)){
     ans=cbind(ans,nominal.scaling.vec(X[,k], add=c(colnames(X)[k],":")))
  }
return(ans)}



dordinal.scaling.vec=function(x,add=NULL){ ## Funktion zur 'dual-ordinalen' Skalierung (also >= anstelle von <= ) eines Vektors
  attr=sort(unique(x))
  m=length(attr)
  n=length(x)
  ans=array(0,c(n,m))
  NAMES=rep("",m)
  t=1
  for(k in (1:m)){
        NAMES[k]=paste(c(add," x>=", attr[k]),collapse="")
        ans[,k]=(x>=attr[k]  )

  }
colnames(ans)=NAMES
return(ans)}

dordinal.scaling=function(X){ ## Funktion zur 'dual-ordinalen' Skalierung (also >= anstelle von <= ) einer datenmatrix
  m=dim(X)[2]
  ans=NULL
  for(k in (1:m)){
     ans=cbind(ans,dordinal.scaling.vec(X[,k], add=c(colnames(X)[k],":")))
  }
return(ans)}

interordinal.scaling=function(X){cbind(ordinal.scaling(X),dordinal.scaling(X))} ## Funktion zur interordinalen einer Datenmatrix

conceptual.scaling.dim=function(dat){  # berechnet die Anzahl benoetigter Merkmale fuer begriffliche Skalierung
  X=dat
  
  n=dim(X)[2]
  K=rep(0,n)
  NAMES=NULL
  CN=colnames(dat)
  class=rep("",n)
  for(k in (1:n)){
   class[k]=class(X[,k])
   if(class(X[,k])[1]=="ordered" | class(X[,k])[1]=="numeric" | class(X[,k])[1]=="integer"){K[k]=2*length(unique(X[,k])); NAMES=c(NAMES,rep(CN[k],K[k]))}
   if(class(X[,k])[1]=="factor"){K[k]=length(unique(X[,k])); NAMES=c(NAMES,rep(CN[k],K[k]))}
  }
return(list(class=class,K=K,dim=sum(K),NAMES=NAMES))}



##########################################
########			     	      ########
#######						       #######
##### Optimization on Closure Systems  #####
#######                            #######
########				          ########
##########################################



extent_opt_a=function(X,gen.index,v,binary.variables="afap"){##  extentopt: Version, wie in VL beschrieben

# X: Kontext
# genindex: Indizes derjeniger Gegengstände, für die das mit diesen Gegenständen und den Merkmalen erzeugte Hüllenstsem von Umfängen/Inhalten betrachtet wird.
# v Zielfunktion
# binary.variables: Methode, welche Variablen auf binär gesetzt werden, um möglichst effiziente Berechnung zu ermöglichen:
# afap: as few as possible: So wenig wie möglich Variablen als binär setzen
# sd: smallest dimension: Entweder alle Varibalen der Gegenstände oder alle variablen der Merkmale auf binär setzen, je nachdemm ob die Anzhal Gegenstände oder die Anzahl Merkmale kleiner ist.
# allgen: setze alle Variabeln der den Verband erzeugenden gegenstände (also alle Gegenstände, die durch gen.index indiziert sind) binär
#all: setze alle Varibalen auf binär


  m=dim(X)[1]
  n=dim(X)[2]
  mask=rep(0,m)
  mask[gen.index]=1
  N=length(which(X==0))+m+n
  A=array(0,c(N, m+n))
  rhs=rep(0,N)
  sense=rep("",N)
  t=1
  for(k in (1:m)){
     for(l in which(X[k,]==0)){
	   A[t,k]=1;A[t,l+m]=1;rhs[t]=1;sense[t]="<="
	   t=t+1
	 }
  }
  
  for(k in (1:m)){A[t,which(X[k,]==0)+m]=1;A[t,k]=1;rhs[t]=1;sense[t]=">=";t=t+1}
  
  for(k in (1:n)){A[t,which(mask==1 & X[,k]==0)]=1;A[t,k+m]=1;sense[t]=">=";rhs[t]=1;t=t+1}
  t=t-1
 
  
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
           
		   
		   
return(list(A=A[(1:t),],rhs=rhs[(1:t)],sense=sense[(1:t)],modelsense="max",lb=rep(0,m+n),ub=rep(1,m+n),obj=c(v,rep(0,n)),vtypes=vtypes))}
   

extent_opt_b=function(X,gen.index,v,binary.variables="afap"){##  extentopt: Version, wie in TR 209, S.23 beschrieben, nur Ungleichungen (21) verschärft

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
  
  for(k in (1:n)){
j=which(mask==1 & X[,k]==0)
if(length(j)>=1){
A[t,which(mask==1 & X[,k]==0)]=1;A[t,k+m]=1;sense[t]=">=";rhs[t]=1;t=t+1}}
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
  
  
return(list(A=as.simple_triplet_matrix(A[(1:t),]),rhs=rhs[(1:t)],sense=sense[(1:t)],modelsense="max",lb=lb,ub=ub,obj=c(v,rep(0,n)),ext.obj=v,intent.obj=rep(0,n),m=m,n=n,vtypes=vtypes,n.constr=t,context=X))}
   
   
   
   
extent_opt_c=function(X,gen.index,v,binary.variables="afap"){##  extentopt: Version, wie extent.opt.b, nur, dass Matrix, die Ungleichungsnebenbedingungen enthält, direkt sofort als simple triplet Matrix erzeugt wird

  m=dim(X)[1]
  n=dim(X)[2]
  mask=rep(0,m)
  mask[gen.index]=1
  N=5*(m+n)
  NN=m*n-sum(X)
  I=rep(as.integer(0),5*NN)
  J=I
  V=I
  
  lb=rep(0,m+n);ub=rep(1,m+n)
  
  rhs=rep(0,N)
  sense=rep("",N)
  t=1
  tt=1
  for(k in (1:m)){
       i=which(X[k,]==0)
	   
	   if(length(i) >=1){
	       L=length(i)
	       I[tt]=t
		   J[tt]=k  ## A[t,k]=L;
		   V[tt]=L
		   tt=tt+1
		   index=(tt:(tt+L-1))
		   I[index]=t
		   J[index]= i+m ###A[t,i+m]=1;
		   V[index]=1
		   
	   	   tt=tt+L
		   rhs[t]=length(i);sense[t]="<="
	       t=t+1
	    }
		else{lb[k]=1}
	 
    }
	
  
  for(k in (1:n)){
       i=which(X[,k]==0)
	   
	   if( length(i) >=1){
	       L=length(i)
	       I[tt]=t
		   J[tt]=k+m   #A[t,k+m]=L
		   V[tt]=L
		   tt=tt+1
	      index=(tt:(tt+L-1))
	   	   I[index]=t
		   J[index]=i  #  A[t,i]=1;
		   V[index]=1
		   tt=tt+L
		   rhs[t]=length(i);sense[t]="<="
	       t=t+1
	    }
	    else{lb[k+m]=1}
    }
	
	
  
  for(k in (1:m)){
 i=which(X[k,]==0)
 L=length(i)
  if(length(i)>=1){
    L=length(i)
	I[tt]=t
	J[tt]=k  #A[t,k]=1;
	V[tt]=1
	
	tt=tt+1
	
	index=(tt:(tt+L-1))
	I[index]=t
	J[index]=i+m  #A[t,i+m]=1;
	V[index]=1
    tt=tt+L
  
    rhs[t]=1;sense[t]=">=";t=t+1
}}



  
  for(k in (1:n)){
j=which(mask==1 & X[,k]==0)


if(length(j) >=1){

  L=length(j)
  
  I[tt]=t
  J[tt]=k+m     #A[t,k+m]=1;
  V[tt]=1
  tt=tt+1
  index=(tt:(tt+L-1))
  I[index]=t
  J[index]=j   #A[t,j]=1;
  V[index]=1
  tt=tt+L
sense[t]=">=";rhs[t]=1;t=t+1}

else{lb[k+m]=1}}

  tt=tt-1
  t=t-1
   
  jj=which(I!=0 &J!=0)
  
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
return(list(A=simple_triplet_matrix(I[jj],J[jj],V[jj],nrow=t,ncol=m+n),rhs=rhs[(1:t)],sense=sense[(1:t)],modelsense="max",lb=lb,ub=ub,obj=c(v,rep(0,n)),ext.obj=v,intent.obj=rep(0,n),m=m,n=n,vtypes=vtypes,n.constr=t,context=X))}
    
 

extent_opt=extent_opt_c  ### standardmaessig wird immer Version extent.opt.c verwendet 



########################

k_extent_opt_b=function(X,gen_index,v,binary_variables="afap",K){##  extentopt: Version, wie TR 209, S.23 beschrieben, nur Ungleichungen (21) verschärft
# berechnet Model zur Optimierun von Zielfunktion v über alle K-Merkmalserzeugte Begriffe
  m=dim(X)[1]
  n=dim(X)[2]
  mask=rep(0,m)
  mask[gen_index]=1
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
  idx=which(colSums(X[gen_index,])==length(gen_index))
  if(length(idx)>0){lb[m+idx]=1}
  
  idx=which(rowSums(X[,])==n)
  if(length(idx)>0){lb[idx]=1}
  
  ###  setze je nach Methode gewisse Variablen als binaer
  vtypes=rep("C",m+n)
  if(binary_variables=="afap"){
       if(length(gen_index)<=min(m,n)){
           vtypes[gen_index]="B"
		}
		if(length(gen_index)>min(m,n) & m<=n){
		    vtypes[(1:m)]="B"
		}
		if(length(gen_index)>min(m,n) & n<=m){
		    vtypes[-(1:m)]="B"
		}
	}	
		   
  if(binary_variables=="sd"){
    if(m<=n){
      vtypes[(1:m)]="B"
    }
    else{vtypes[-(1:m)]="B"}
  }

  if(binary_variables=="allgen"){
    vtypes[gen.index]="B"
    vtypes[-(1:m)]="B"
  }
  
  if(binary_variables=="all"){
    vtypes=rep("B",m+n)
  }
  
  if(  !(binary_variables %in% c("afap","sd","allgen","all"))){print("invalid argument for binary.variabes")}
  
  A=rbind(A[(1:t),],c(rep(0,m),rep(1,n)))
  rhs=c(rhs[(1:t)],K)
  sense=c(sense[(1:t)],"<")
  ##Über vtypes nochmalnachdenken:
  
  vtypes[(1:m)]="C"
  vtypes[-(1:m)]="B"
  
return(list(A=as.simple_triplet_matrix(A),rhs=rhs,sense=sense,modelsense="max",lb=lb,ub=ub,obj=c(v,rep(0,n)),ext.obj=v,intent.obj=rep(0,n),m=m,n=n,vtypes=vtypes,n.constr=t,context=X))}




########################  
  
test_extent_opt=function(method,M=10,N=5,p=0.5,M1=5,binary_variables="afap"){  ## testet auf Korrektheit der Funktion extent.opt
  X=random_context(M=M,N=N,p=p)#runif(M*N)>=0.5;dim(X)=c(M,N)
  i=sample((1:M),size=round(M/2,0),replace=FALSE)
  
  idx=sample((1:M),size=M1,replace=FALSE)
  v=rep(0,M)
  v[idx]=1/M1
  v[-idx]=-1/(M-M1)
  L2=concept.lattice(X[i,])
  n=dim(L2$intents)[1]
  a=rep(0,n)
  for(k in (1:n)){
   temp=0
   for(l in (1:M)){
     if(all(X[l,]>= L2$intents[k,])){temp=temp+v[l]}
	}
	a[k]=temp
 }

 temp=method(X,gen_index=i,v=v,binary_variables=binary_variables)
 result=(gurobi(temp,list(OutputFlag=0)))
 ans1=result$objval
 ans2=(max(a))
 
 X <<- X*1
 i <<- i
 v <<- v
 temp <<-temp
 ans1 <<- ans1
 ans2 <<- ans2 
 i <<- i
return(abs(ans1-ans2) <= 10^-9)}

  
###################################

min_k_attr_generated=function(extent,intent,X){  # Berecchnet für Begriff gegeben durch Umfang extent und Inhalt intent das maximale k, für das der Begriff k-Merkmalserzeugt ist (Kontext X muss ebenfalls mit übergeben werden)
  m=dim(X)[1]
  n=dim(X)[2]
  model=k_extent_opt_b(X,(1:m),(1:m),K=dim(X)[2])
  model$lb[which(extent==1)]=1
  model$ub[which(extent==0)]=0
  model$ub[which(intent==0)+m]=0
  model$obj=c(rep(0,m),rep(1,n))
  model$modelsense="min"
  return(model)}


min_k_obj_generated=function(extent,intent,X){min_k_attr_generated(intent,extent,t(X))} # Berecchnet für Begriff gegeben durch Umfang extent und Inhalt intent das maximale k, für das der Begriff k-MGegenstandserzeugt ist (Kontext X muss ebenfalls mit übergeben werden)
  
  
 








##########################################
########			     	      ########
#######						       #######
######  Subgroup Discovery  in FCA  ######
#######                            #######
########				          ########
##########################################




col.reduce=function(X){   ##doppelt???
  
  m=dim(X)[1]
  n=dim(X)[2]
  t=1
  ans=rep(0,n)
  for(k in (1:n)){
    T=rep(0,n)
    T[k]=1
    TT=H.attr(T,bg=list(context=X))
    TT[k]=0
    U1=PHI(TT,bg=list(context=X))
    if(sum(X[,k])==m | any(U1!=X[,k])){ans[t]=k;t=t+1}
  }
  t=t-1
return(X[,ans[(1:t)]])}

col.reduce.indexs=function(X){
  first=TRUE
  m=dim(X)[1]
  n=dim(X)[2]
  t=1
  ans=rep(0,n)
  for(k in (1:n)){
    T=rep(0,n)
    T[k]=1
    TT=H.attr(T,bg=list(context=X))
    TT[k]=0
    U1=PHI(TT,bg=list(context=X))
    if( (sum(X[,k])==m &first)| any(U1!=X[,k])){ans[t]=k;t=t+1;first=FALSE}
  }
  t=t-1
return(ans[(1:t)])}


col.clarify=function(X){ t(unique(t(X)))}

remove.full.cols=function(X){
  m=dim(X)[1]
  CS=colSums(X)
return(X[,which(CS!=m)])}

remove.full.rows=function(X){
  n=dim(X)[2]
  CS=colSums(X)
  RS=rowSums(X)
return(X[,which(RS!=n)])}






subgroup_discovery_fca_milp=function(dat,target,target.class,nrep,heuristic,remove.full.columns=TRUE,clarify.cols=FALSE,reduce.cols=FALSE,weighted=FALSE,small){ #Fuehrt Subgroup Discovery durch (erzeugt nur MILP, das dann noch mit z.B. gurobi(...) gelöst werden muss
   XX=dat
   XX[[target]]=NULL
   print(objects(XX))
   X=conceptual.scaling(XX)
   print("E")
   

   
   print(c("dim dat: ",dim(dat)),quote=FALSE)
   print(c("dim X (conceptual scaling dat):     ",dim(X)),quote=FALSE)
   
   if(remove.full.columns){
     X=remove.full.cols(X)
     print(c("dim X without full columns:         ",dim(X)),quote=FALSE)
   }
   if(clarify.cols){
     X=col.clarify(X)
     print(c("dim X without doubled columns:      ",dim(X)),quote=FALSE)
   }
   if(reduce.cols){
     X=col.reduce(X)
     print(c("dim final X (clarified and reduced):",dim(X)),quote=FALSE)
   }
   
   
   m=dim(X)[1]
   n=dim(X)[2]
   
   M=dim(XX)[2]
   
    # A=NULL
    # A=array(0,c(2*n,m+n))
    # t=1
    # T=1
    # for(k in (1:M)){
      # K=length(unique(XX[,k]))
	  # #print(K)
	  # temp=rep(0,c(m+n))
	  # if(class(XX[,k])[1]=="factor"){
	 
	    # temp[((t+m):(t+m+K-1))]=1
	    # A[t,]=temp
	    # T=T+1
	    # #A=rbind(A,temp)
	   
	    # t=t+K
	  # }
	 
	  # if(class(XX[,k])[1]=="ordered" | class(XX[,k])[1]=="numeric" | class(XX[,k])[1]=="integer"){
	 
	    # for(l in (1:(K-1))){
	       # temp[t+m+l-1]=1
	       # temp[t+m+l]=-1
		   # A[T,]=temp
		   # T=T+1
		   # #A=rbind(A,temp)
		  
		   # temp=rep(0,c(m+n))
	       # temp[t+m+l-1+K]=-1
		   # temp[t+m+l+K]=1
		   # A[T,]=temp
		   # T=T+1
		   # #=rbind(A,temp)
		  # }
	     # t=t+2*K
	  # }
	 
	 
	 
	  # #t=t+K
	 # }
	 # T=T-1
	 # A=A[(1:T),]
	#A=NULL
    v = (dat[[target]]==target.class)-(dat[[target]]!=target.class)*mean(dat[[target]]==target.class)/mean(dat[[target]]!=target.class)
	if(weighted){
	   W=weighted.repr(X,v)
	    v=W$yw
        
	    X=W$Xw
	 }
	 
	 else{W=list(count=rep(1,dim(X)[1]))}
	 
	 v <<- v
	 m=dim(X)[1]
	 n=dim(X)[2]
	 print("building model...")
	 if(small){
     ans=extent.opt(X,which(v>0),v) }
	 else{ans=extent.opt(X,(1:m),v) }
	 print("...done")
	 #M=dim(A)[1]
	 #ans$A=rbind(ans$A,A);ans$rhs=c(ans$rhs,rep(1,M));ans$sense=c(ans$sense,rep("<=",M))
	 print(system.time(temp <- heuristic(X,v,nrep=nrep)))
	 CUT=ceiling(temp$objval)
	 print(CUT)
	 
	 T=rep(0,n+m)
	 T[(which(v> 0))]=-W$count[which(v>0)]
	 #ans$A=rbind(ans$A,matrix(T,nrow=1))
	 #ans$rhs=c(ans$rhs,-CUT)
	 #ans$sense=c(ans$sense,"<=")
	 ans$start=c(temp$solution,PSI(temp$solution,context=X))
	 ans$context=X
	 ans$NAMES=conceptual.scaling.dim(XX)$NAMES
	 #TEMP=heuristic.implications(X,v,NREP)
	 
	 #ans$A=rbind(ans$A,TEMP$A);ans$rhs=c(ans$rhs,TEMP$rhs);ans$sense=c(ans$sense,TEMP$sense)
	 
	 #ans$vtypes[which(ans$start>=0.5)]="B"
	 #ans$vtypes=rep("B",length(ans$vtypes))
return(ans)}

	#a=sd.new(dat,"class","won",1)

quality=function(sdtask,result,NAMES=colnames(sdtask$context)){  ## berechnet Piatetsky-Shapiro-Qualitätsfunktion für bereits geloestes Model (Variable result). Variable sdtask ist erzeugtes Modell aus Funktion subgroup.discovery.fca.milp
  m=sdtask$m
  
  idx=which(result$x[(1:m)]>0.5)
  jdx=which(result$x[-(1:m)]>0.5)
  n0=length(which(sdtask$obj[(1:m)]>0))
  n=length(idx)
  p=length(which(sdtask$obj[(1:m)]>0 & result$x[(1:m)]>0.5))/n
  p0=length(which(sdtask$obj>0))/m
  return(list(n=n,n0=n0,p=p,p0=p0,ps=n*(p-p0),obj=result$objval,argmax=NAMES[jdx]))}
   

heuristic1=function(X,v,nrep){
  set.seed(1234567)
  bg=list(context=X)
  i=which(v>0)
  bg2=list(context=X[i,])
  m=dim(X)[1]
  n=length(i)
  objval=-Inf
  N=dim(X)[2]
  for(k in (1:nrep)){
    if(k<=N ){temp=rep(0,N);temp[k]=1;T=PHI(H.attr(temp,bg2),bg)}
	else{size=sample((1:n))
	j=sample((1:n),size=size)
	temp=rep(0,n)
	temp[j]=1
	#print(length(temp))
	T=PHI(PSI(temp,bg2),bg)
	#print(length(T))
	}
    tempval=sum(v*T)
	#print(tempval)
	if(tempval>objval){objval=tempval;solution=T}
}
return(list(solution=solution,objval=objval))}


heuristic1b=function(X,v,nrep){
  bg=list(context=X)
  i=which(v>0)
  ii=which(v<=0)
  n=dim(X)[1]
  N=length(i)#n=dim(X)[1]#length(i)
  objval=-Inf
  for(k in (1:nrep)){
    size=sample((1:N))
	j=sample((1:N),size=size)
	temp=rep(0,n)
	temp[j]=1
	T=g(temp,bg=list(context=t(X[c(i,ii),])))$x#PHI(PSI(temp,bg),bg)
	TT=rep(0,n)
	TT[i]=T[(1:N)]
	TT[ii]=T[-(1:N)]
	#print(v[which(T==1)])#length(T))
	#print(unique(T))
    tempval=sum(v*TT)#[c(i,ii)]*T)#PHI(T,bg))
	#print(tempval)
	if(tempval>objval){objval=tempval;solution=TT}
}
return(list(solution=solution,objval=objval))}




heuristic.implications=function(X,v,nrep){
  bg=list(context=X)
  i=which(v>0)
  m=dim(X)[1]
  N=dim(X)[2]
  n=length(i)
  objval=-Inf
  ans=array(0,c(nrep,m+N))
  rhs=rep(0,nrep)
  sense=c("",nrep)
  t=1
  for(k in (1:nrep)){
    size=sample((1:n))
	j=sample((1:n),size=size)
	temp=rep(0,m)
	temp[i[j]]=1
	T=PHI(PSI(temp,bg),bg)
	I=which(T==1 & temp !=1)
	J=which(temp==1)
	
	
	if(length(I)>=1){
	  temp2=rep(0,m+N)
	  temp2[J]=1
	  temp2[I]=-1/length(I)
	  rhs[t]=length(J)-1
	  sense[t]="<="
	  ans[t,]=temp2
	  #print("ee")
	  t=t+1
	 }
	
	
}
t=t-1
#print(t)
return(list(A=ans[(1:t),],rhs=rhs[(1:t)],sense=sense[(1:t)]))}


heuristic2=function(X,v,nrep){
  bg=list(context=X)
  i=which(v>0)
  n=length(i)
  objval=-Inf
  weights=v[i]
    
  for(k in (1:nrep)){
    a=runif(1)
    j=runif(n)>=weights*a
    temp=rep(0,m)
	temp[i[j]]=1
	T=PHI(PSI(temp,bg),bg)
    tempval=sum(v*T)
	#print(tempval)
	if(tempval>objval){weights[which(T[i]==1)]=weights[which(T[i]==1)]*alpha;weights=weights/max(weights);objval=tempval;solution=T}
}
return(list(solution=solution,objval=objval))}




weighted.repr=function(X,y = rep(1,dim(X)[1])){   ## computes weigthed representation of a data matrix X with duplicated rows,
                                                  ##  returns unique(X) together with counts: how often appears the column, mean.y: mean of y in the set of the duplicated columns
  Xd=data.frame(cbind(X,y))
  names(Xd)[1]="V1"
  p=dim(X)[2]
  ans=as.matrix(ddply(Xd,names(Xd[(1:p)]),summarise,count=length(V1),mean.y=mean(y),sum.y=sum(y)))
return(list(Xw=ans[,(1:p)], yw=ans[,p+3],mean.y=ans[,p+2],count=ans[,p+1]))}






##########################################
########			     	      ########
#######						       #######
######     Konvexe Mengen           ######
#######                            #######
########				          ########
##########################################


Drehmatrix=function(alpha){t(rbind(c(cos(alpha),-sin(alpha)),c(sin(alpha),cos(alpha))))}  ## Erzeugt Matrix, die Drehung um Winkel alpha bewirkt qua X \mapsto X %*% Drehmatrix(alpha)

convex.incidence=function(X){  ## gegeben Puntmenge von M Punkten in R^2 (uebergeben als M x 2 Matrix X), wird Kontext mit G= Menge der R^2 Punkte und M = Menge aller durch je zwei verschiedene Punkte aus G beschriebenen Halbräume sowie gIm iff Punkt g liegt in (abgeschlossenem) Halbraum m 
  n=dim(X)[1]
  m=n*(n-1)/2
  I1=array(0,c(n,m))
  I2=I1
  t=1
  indexs=array(0,c(m,2))
  NAMES=rep("",m)
  NAMES2=rep("",m)
  for(k in (1:(n-1))){
  print(k)
     for(l in ((k+1):n)){
	   NAMES[t]=paste(rownames(X)[c(k,l)],collapse="")
	   NAMES2[t]=paste(rownames(X)[c(l,k)],collapse="")
	   
        for(M in (1:n)){
           v1=X[k,]-X[l,]
           v2=X[M,]-X[l,]
           indexs[t,]=c(k,l)
           s=v1[1]*v2[2]-v1[2]*v2[1]
           if(s>0){I1[M,t]=1}
           if(s<0){I2[M,t]=1}
           if(s==0){I2[M,t]=1;I1[M,t]=1}
        }
        t=t+1
     }
  }
  colnames(I1)=NAMES
  colnames(I2)=NAMES2
  rownames(I1)=rownames(X)
  rownames(I2)=rownames(X)
  
return(list(context=(cbind(I1,I2)),indexs=rbind(indexs,indexs),X=X))}



convex.implications=function(bg){
  n=dim(bg$context)[2]
  ans=list()
  ans$premise=simple_triplet_zero_matrix(nrow=2*n^4,ncol=n)#as.logical(0),nr=2*n^4/4,nc=n)
   T=1
  ans$conclusion=simple_triplet_zero_matrix(nrow=2*n^4,ncol=n)#matrix((0),nr=2*n^4,nc=n)
  print("e")
  for(k in (1:(n-2))){
    print(k)
     for(l in ((k+1):(n-1))){
      
        m=n-l
        I=array(0,c(n,n))
        diag(I)=1
        for(t in (1:n)[-c(k,l)]){
            temp=rep(0,n)
            temp[k]=1
            temp[l]=1
            temp[t]=1
            H=H.attr(temp,bg)
            I[t,which(H==1&temp==0 )]=1
            temp[t]=0
         }   
         J=neighbour.incidence(I)
         diag(J)=0
         indexs=which(J==1,arr.ind=TRUE)
         M=dim(indexs)[1]
            if(M!=0){
              for(u in (1:M)){
               if(indexs[u,1]>l){
                temp2=rep(0,n)
                temp2[c(k,l)]=1
                temp2[indexs[u,1]]=1
                ans$premise[T,(1:n)]=as.logical(temp2)
                temp2=rep(0,n)
                temp2[indexs[u,2]]=1
                ans$conclusion[T,(1:n)]=as.logical(temp2)
                T=T+1
              }  
             }
            }
            
        
     }
  }
  T=T-1
  ans$premise=ans$premise[(1:T),(1:n)]
  ans$conclusion=ans$conclusion[(1:T),(1:n)]
return(ans)}



convex.generic.base=function(bg,HOP=convex.H.obj2){ # berechnet generische Basis fuer Kontext von konvexen Mengen in R^2
								  #vgl. Bastide et al. 2000
  M=dim(bg$context)[1]
  ans=list()
  N=choose(M,3)
  ans$premise=(array(as.logical(0),c(N,M)))
  ans$conclusion=(array(as.logical(0),c(N,M)))
  t=1
  for(k in (1:(M-2))){
  print(k)
    for(l in ((k+1):(M-1))){
      for(m in ((l+1):M)){
	  
        temp=rep((0),M)
		
        temp[c(k,l,m)]=1
		
        H=HOP(temp,bg)
		
        H[c(k,l,m)]=0
		
        ans$premise[t,(1:M)]=(temp)
		
        ans$conclusion[t,(1:M)]=(H)
		#print(M)
        t=t+1
		
      }
    }
  }
return(ans)}


        
          
MILP.from.implications=function(implications,binary=TRUE){## fuer lpSolveAPI
  m=dim(implications$premise)[1]
  m2=dim(implications$premise)[2]
  n=sum(implications$conclusion)
  LP=make.lp(nrow=n+m2,ncol=m2)
  for(k in (1:m)){
    index=which(implications$premise[k,]==1)
    l.index=length(index)
    for(l in which(implications$conclusion[k,]==1)){
      add.constraint(lprec=LP,xt=c(1,rep(-1,l.index)),type=">=",rhs=-(l.index-1),indices=c(l,index))
    }
  }
  for(k in (1:(m2))){
    add.constraint(lprec=LP,xt=c(1),type="<=",rhs=1,indices=c(k))
  }

if(binary){for(k in (1:m2)){set.type(LP,"binary")} }
return(LP)}

MILP.from.implications=function(implications,binary=TRUE){## fuer lpSolveAPI
  m=dim(implications$premise)[1]
  m2=dim(implications$premise)[2]
  n=sum(implications$conclusion)
  A=array(0,c(m,m2))
  rhs=rep(0,m)
  #LP=make.lp(nrow=n+m2,ncol=m2)
  for(k in (1:m)){
    index=which(implications$premise[k,]==1)
	jndex=which(implications$conclusion[k,]==1)
    l.index=length(index)
	l.jndex=length(jndex)
    
	A[k,index]=1
	A[k,jndex]=-1/l.jndex
	rhs[k]=l.index-1
      #add.constraint(lprec=LP,xt=c(1,rep(-1,l.index)),type=">=",rhs=-(l.index-1),indices=c(l,index))
    }
  #}
  #for(k in (1:(m2))){
  #  add.constraint(lprec=LP,xt=c(1),type="<=",rhs=1,indices=c(k))
  #}

#if(binary){for(k in (1:m2)){set.type(LP,"binary")} }
return(list(A=A,lb=rep(0,m2),ub=rep(1,m2),vtypes=rep("B",m2),modelsense="max",sense=rep("<",m),rhs=rhs))}
      
      
MILP.from.generic.base.from.convex.incidence=function(bg,binary=TRUE,max.card=dim(bg$context)[2],DIST,maxdist,HOP=convex.H.obj2){

## erzeugt MILP Model ueber die Implementation von Contsraints, die das Repsektieren der generischen (Gegenstands-) Implikationsbasis sicherstellen

                          ##hieß früher LP.from.convex.incidence.simple
						  
# bg:Liste mit Objekt context, das Kontext und Objekt X, das ursprüngliche Datenmatrix X enthält

  n=dim(bg$context)[1]
  N=choose(n,3)
  T=1
  tt=1
   D=rep(0,N)
  ii=rep(1/2,floor(N*n/2.5))
  jj=  rep(1/2,floor(N*n/2.5))
  vvv=rep(1/2,floor(N*n/2.5))
  tt=1
  indexs=array(0,c(N,3))
   # A <-simple_triplet_matrix(1,1,0,nrow=N,ncol=n)# sparseMatrix((0),nr=N,nc=n)# Matrix(nrow=N,ncol=n,sparse=TRUE)#simple_triplet_zero_matrix(nrow=N,ncol=n)#simple_sparse_array(i=0,v=0,dim=c(N,n))#,sparse=TRUE)#array(as.logical(0),c(N,n))
    #sparseMatrix(i=2*n^4,j=n,dims=c(2*n^4,n))#sparseMatrix((0),nr=2*n^4,nc=n)
    rhs=rep(0,N)
    sense=rep(">=",N)
  for(k in (1:(n-2))){
     print(k)
     for( l in ((k+1):(n-1))){
     if(DIST[k,l]<=maxdist){
        for(m in ((l+1):n)){
        if(DIST[k,l]<maxdist & DIST[m,l]<=maxdist){
            temp=rep(0,n)
            temp[k]=1
            temp[l]=1
            temp[m]=1
            D[T]=max(DIST[k,l],DIST[k,m],DIST[l,m])
			H=HOP(temp,bg)#H.attr(temp,bg)HULL(k,l,m,bg)#H.attr(temp,bg)
            H[c(k,l,m)]=0
            i=which(H==1)
            j=length(i)
            if(j!=0){
            
            
             ii[(tt:(tt+j-1))] <- T
             jj[(tt:(tt+j-1))] <- i
             vvv[(tt:(tt+j-1))]<- 1/j
             tt=tt+j
             
             ii[(tt:(tt+2))]=T
             jj[(tt:(tt+2))]=c(k,l,m)
             vvv[(tt:(tt+2))]=-1
              tt=tt+3
             
            
              #A[T,i]=1/j
              sense[T]=">="
              #A[T,c(k,l,m)]=-1
              rhs[T]=-2
              
			  indexs[T,]=c(k,l,m)
			  T=T+1
            }

           }}} }}
           T=T-1
           tt=tt-3
          ii=ii[(1:tt)]
          jj=jj[(1:tt)]
          vvv=vvv[(1:tt)]
          gc()
       model=list(A=simple_triplet_matrix(i=ii[(1:tt)],j=jj[(1:tt)],v=vvv[(1:tt)])  ,obj=NULL,modelsense="max",rhs=rhs[(1:T)],sense= sense[(1:T)],vtypes=rep('B',n) ,D=D,indexs=indexs)
       
       return(model=model)}

      
  #############

convex.H.obj=function(A,bg){## Huellenoperator Phi \circ Psi speziell fuer einen Geomtrie-Kontext (also mit G= Punkte in R^2 und M Halbräume
							## benötigt Package geometry
if(sum(A)<=2){return(A)}
P=convhulln(bg$X[which(A==1),])
ans=inhulln(P,bg$X)
return(ans*1)}




convex.H.obj2=function(A,bg){ ##  benötigt Package geometry und Package Biobase, macht das gleiche wie  convex.H.obj, scheint aber oft schneller zu sein als convex.H.obj
A <<- A
temp=cart2bary(bg$X[as.logical(A),],bg$X)
if(is.null(temp)){print("warning: degenerate simplex");return(H.obj(A,bg))}
temp2=rowMin(temp)>=0
return(temp2*1)}



simplify.geometry.model=function(model){### vereinfact Geometrie-Modell. geht nur wenn Zielfunktion bereits spezifiziert (in modelobj).
										### Es werden alle Implikationen, für die die Prämisse mindestens eine Variable enthält, für die die Zielfunktion negativ ist, entfernt. geht nur für generische Basis. Beweis dafür, dass das funktioniert, ist noch nicht geführt.
  m=dim(model$A)[1]
  n=dim(model$A)[2]
  
 idx=rep(1,m)
 negative.indexs=which(model$obj<0)
 
 for( k in (1:m)){ if(any(model$indexs[k,] %in%negative.indexs)){idx[k]=0}}#temp=which(as.vector(model$A[k,(1:n)])<0);if(any(v[temp]<0)){idx[k]=0}}
 
 idx=which(idx==1)
 ans=model
 ans$A=model$A[idx,(1:n)]
 ans$sense=model$sense[idx]
 ans$rhs=ans$rhs[idx]
 return(ans)}
 
###################  


simplify.geometry.model2=function(modell){### vereinfact Geometrie-Modell. geht nur wenn Zielfunktion bereits spezifiziert (in modelobj).
										### Es werden alle Implikationen, für die die Prämisse mindestens eine Variable enthält, für die die Zielfunktion negativ ist, entfernt. geht nur für generische Basis. Beweis dafür, dass das funktioniert, ist noch nicht geführt.
  model=modell										
  m=dim(model$A)[1]
  n=dim(model$A)[2]
  
 idx=rep(0,m)
 negative.indexs=which(model$obj<0)

 
 for( k in (1:m)){ if( !any(model$indexs[k,] %in%negative.indexs)){
  
 idx[k]=1
 i=which(model$A[k,(1:n)]>0)
 #print("f")
 j=which(model$A[k,(1:n)]>0 & model$obj<0)
 #print(j)
 if(length(j)>0){
 model$A[k,i]=rep(0,length(i))
 model$A[k,j]=rep(1/length(j),length(j))
 }
 }
 }
 #}#temp=which(as.vector(model$A[k,(1:n)])<0);if(any(v[temp]<0)){idx[k]=0}}
 
 idx=which(idx==1)
 ans=model
 ans$A=model$A[idx,(1:n)]
 ans$sense=model$sense[idx]
 ans$rhs=ans$rhs[idx]
 return(ans)}
 
###################  
      
      

MILP.from.minmin.base.from.convex.incidence=function(bg,binary=TRUE,max.card=dim(bg$context)[1],DIST,maxdist){
  NN=choose(dim(bg$context)[1],3)*dim(bg$context)[1]/5
  m=dim(bg$context)[1]
  #LP=make.lp(nrow=1,ncol=n)
  
   T=1
    A=array(as.logical(0),c(NN,m))#sparseMatrix(i=2*n^4,j=n,dims=c(2*n^4,n))#sparseMatrix((0),nr=2*n^4,nc=n)
    rhs=rep(0,NN)
  for(k in (1:(m-2))){
     print(k)
     second.indexs=which(DIST[k,]<=maxdist)
     #print(second.indexs[-(1:k)])
     for(l in setdiff(second.indexs,(1:k))){
        
        I=array(0,c(m,m))
        diag(I)=1
        third.indexs=which(DIST[k,]<=maxdist +000& DIST[l,]<=maxdist+000) 
        for(t in setdiff(third.indexs,c(k,l))){
            temp=rep(0,m)
            temp[k]=1
            temp[l]=1
            temp[t]=1
            H=H.obj(temp,bg)
            if(length(      which(H==1&temp==0 ))>0){   I[t,which(H==1&temp==0 )]=1 }
            temp[t]=0
         }   #I[t,c(k,l)]=0
         J=neighbour.incidence(I)
         diag(J)=0
         indexs=which(J==1,arr.ind=TRUE)
         M=dim(indexs)[1]
         
            if(M!=0){
              for(u in (1:M)){
               #H=rep(0,n)
               #H[c(k,l,indexs[u,1])]=1
               #H=H.attr(H,bg)
               if( TRUE | indexs[u,1]>l){# & sum(H) <= max.card & max(DIST[k,l],DIST[k,indexs[u,1]],DIST[l,indexs[u,1]]) <= maxdist){
               
                
               # add.constraint(lprec=LP,xt=c(1,-1,-1,-1),type=">=",rhs=-2,indices=c(indexs[u,2],k,l,indexs[u,1]))
                #if(k==27 &l ==30 &(TRUE|indexs[u,1]==39)){print("GGGGGGGG")}
                A[T,indexs[u,2]]=1
                A[T,k]=-1
                A[T,l]=-1
                A[T,indexs[u,1]]=-1
                rhs[T]=-2
                
                
               
                T=T+1
                 if(T>NN){print(T);T=T-1;model=list(A=A[(1:T),],obj=NULL,modelsense="max",rhs=rhs[(1:T)],sense= rep('>',T),vtypes=rep('B',m) );return(list(model=model))}
             }
            }
            
        
     }
  } }
  T=T-1
  #if(binary){set.type(LP,(1:n),"binary")}
  model=list(A=as.simple_triplet_matrix(A[(1:T),]),obj=NULL,modelsense="min",rhs=rhs[(1:T)],sense= rep('>',T),vtypes=rep('B',m) )
return(list(model=model))}


diameter.model=function(i,j,model,X,D=as.matrix(dist(X))){###  Berechnet Model zu Bestimmung großer Kontranominalskalen im Geometrie-Kontext. Es wird angenommen, dass KNS Punkte i und j enthält und dass der Durchmesser der KNS durch die Punkte i und j gegeben ist. Außerdem wird nur Teil links von Durchmesser ij berechnet, d.h. Punkte, die auf der rechten Seite von ij liegen werden nicht berücksichtigt. außerdem werden auch Punkte, die zu weit weg liegen (so dass Durchmesser nicht mehr ij sein kann), ebenfalls nicht betrachtet
	nij=(X[j,]-X[i,])/D[i,j]
	m=dim(X)[1]
	idx=rep(0,m)
	
	for(k in (1:m)[-c(i,j)]){
	   vik=(X[k,]-X[i,])
	   
	   #y2*x1-y1*x2,
	   
	   if( (X[k,2]-X[i,2])*(X[j,1]-X[i,1])-(X[j,2]-X[i,2])*(X[k,1]-X[i,1])<0 |(nij%*%vik) <0 | D[i,k]>D[i,j] | D[j,k]>D[i,j]){idx[k]=1}
	}
	
	ans=model
	ans$ub[which(idx==1)]=0
	ans$lb[c(i,j)]=1
return(ans)}






plot.implications=function(implications,names=(1:(dim(implications$premise)[2]))){
  m=dim(implications$premise)[1]
  for(k in (1:m)){
    if(all(implications$premise[k,]==0)){print(paste(c("{}",  "  ==>  ", names[which(implications$conclusion[k,]==1)]),collapse=" "))} 
    else{print(paste(c(names[which(implications$premise[k,]==1)], "  ==>  ", names[which(implications$conclusion[k,]==1)]),collapse=" "))} 
   }
 }    







 
 
##########################################
########			     	      ########
#######						       #######
######     Quantile in FBA          ######
#######                            #######
########				          ########
##########################################
 
 
context.levels=function(X){  ### berechnet Levelfunktion fuer begriffliches Quantilkonzept
  n=dim(X)[1]

  A=colSums(X)
  B=as.vector(n-A)
  l=rep(0,n)
  for(k in (1:n)){
    temp=X[k,]
    l[k]=max(B[which(temp==1)])
  }
  F=ecdf(l)
return(F(l))} 



##########################################
########			     	      ########
#######						       #######
######     VC-theorie und FBA       ######
#######                            #######
########				          ########
########################################## 


VC.impl=function(imp){## berechnet VC-Dimension eines Huellensystems, das durch ein Implikationsbasis imp gegeben ist. Achtung: Geht nicht fuer jede Basis. Konklusionen der Implikationen der Basis muessen maximimal bezueglich Mengeninklusion (bezogen auf das System aller geltenden Implikationen (nicht einer Basis)) sein
  m=dim(imp$premise)[1]
  n=dim(imp$premise)[2]
  A=array(0,c(m,n))
  rhs=rep(0,m)
  for(k in (1:m)){
    temp=which(imp$premise[k,]==1)
    rhs[k]=length(temp)
    A[k,temp]=1
    temp=which(imp$conclusion[k,]==1)
    A[k,temp]=1/sum(temp)
  }
return(list(A=A,rhs=rhs,lb=rep(0,n),ub=rep(1,n),vtypes=rep("B",n),sense=rep("<",m),modelsense="max",obj=rep(1,n)))}

extent_VC=function(X,additional.constraint=TRUE){  # Berechnet VC-Dimension eines Kontextes X
  m=dim(X)[1]
  n=dim(X)[2]
  ans=list()
  ans$A=array(0,c(2*(m+n),m+n))
  ans$rhs=rep(0,2*(m+n))
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
    
    
ans$modelsense="max"
ans$lb=rep(0,m+n)
ans$ub=rep(1,m+n)
ans$vtypes=c(rep("B",m),rep("B",n))
ans$obj=c(rep(1,m),rep(0,n))   

ans$A=rbind(ans$A,c(rep(1,m),rep(0,n)),c(rep(0,m),rep(1,n)),rep(1,m+n))
ans$rhs=c(ans$rhs,min(m,n),min(m,n),n+m)
ans$sense=c(ans$sense,"<=","<=","<=") 

if(additional.constraint){
  ans$A=rbind(ans$A,c(rep(-1,m),rep(1,n)))
  ans$rhs=c(ans$rhs,0)
  ans$sense=c(ans$sense,"=")
  }
return(ans)}



local_object_VCdims=function(X,indexs=(1:dim(X)[1]),outputflag,timelimit,pool=FALSE,transpose=TRUE,additional.constraint=TRUE,threads=1){
# Berechnet lokale Gegenstands-VC-dimension:
# X : Kontext
# indexs: Indizes derjenigen Punkte, für die die lokale Gegenstands-VC-Dimension berechnet werden soll
# outputflag: Argument, das an urobi übergeben wird (zur Steuerung der Ausgabe während der Berechnung)
# timelimit: Zeitlimit für die Berechnun einer einzelnen lokalen VC-Dimension
# pool: Wenn True, dann werden alle Kontranominalskalen maximaler Kardinalität berechnet, ansonsten nur eine
# Transpose: ob Kontext vorher transponiert werden soll: Bei Kontext mit mehr Zeilen als Spalten scheint mit transpose =TRUE die Berechnung schneller zu laufen, für mehr Spalten als Zeilen scheint transpose=FALSE oft schneller zu sein
#additional.constraint: ob zusätzlicher Constraint (Anzahl Gegenstände der Kontranominalskala==Anzahl Merkmele der Kontranominalskala) mit implementiert werden soll (dadurch wird Berechnung oft leicht schneller)

  m=dim(X)[1]
  n=dim(X)[2]
  ans=list()
  vcdims=rep(0,m)
  vccounts=rep(0,m)
  for(k in indexs){
    if(transpose){
	  temp=extent_VC(t(X),additional.constraint=additional.constraint)
      temp$lb[k+n]=1
	}
	else{
	temp=extent.VC((X))
    temp$lb[k]=1
	}
	
    
    if(pool){a=gurobi(temp,list(outputflag=outputflag,timelimit=timelimit,PoolSolutions=100000000,PoolSearchMode=2,Poolgap=0.00001))}
	else{a=gurobi(temp,list(outputflag=outputflag,timelimit=timelimit,threads=threads))}
	a <<- a
    ans[[k]]=a	
    vcdims[k]=a$objval
    vccounts[k]=length(a$pool)
	print(a$objval)
}
return(list(vcdims=vcdims,vccounts=vccounts,rest=ans))}




local_object_VCdims.Hannah=function(X,indexs=(1:dim(X)[1]),outputflag,timelimit,pool=FALSE,transpose=TRUE,additional.constraint=TRUE){
  m=dim(X)[1]
  n=dim(X)[2]
  ans=list()
  vcdims=rep(0,m)
  vccounts=rep(0,m)
  for(k in indexs){
    i=which(X[k,]==1)
    if(transpose){
	
	  
	  temp=extent.VC(t(X[,i]),additional.constraint=additional.constraint)
      
	}
	else{
	temp=extent.VC(X[,i],additional.constraint=FALSE)
    
	}
	
    
    if(pool){a=gurobi(temp,list(outputflag=outputflag,timelimit=timelimit,PoolSolutions=100000000,PoolSearchMode=2,Poolgap=0.00001))}
	else{a=gurobi(temp,list(outputflag=outputflag,timelimit=timelimit))}
	
    	
    vcdims[k]=a$objval
    vccounts[k]=length(a$pool)
	print(a$objval)
}
return(list(vcdims=vcdims,vccounts=vccounts,rest=ans))}


projection.size=function(indexs,S){dim(unique(S[,indexs]))[1]}  #Berechnet S_A für gegebenes Mengensystem S und Projektionsmenge A gegeben durch Indizes der Elemente von A (indexs)

is.shatterable=function(indexs,S){projection.size(indexs,S)==2^length(indexs)}#  Entscheidet, ob Menge A gegeben durch Indizes indexs bezogen auf S shatterable ist



homogenious.context=function(VC=4,shift=2,ncontranominalscales=10*VC,nrow=VC*10*VC,ncol=shift*10*VC+shift,rest=0){##  erzeugt Kontaxt, der von den lokalen VC-Dimensionen rehct homogen ist


ans=runif(nrow*ncol)<=rest;dim(ans)=c(nrow,ncol)

KNS=array(1,c(VC,VC))
diag(KNS)=0
t=1
for(k in (1:ncontranominalscales)){
  ans[(t:(t+VC-1)),(((k-1)*shift+1) : ((k-1)*shift+VC))]=KNS
  t=t+VC
}
return(ans)}


 


##########################################
########			     	      ########
#######						       #######
######   Metrische Aspekte in FBA   ######
#######                            #######
########				          ########
########################################## 

object_dist=function(i,j,context){
  m=dim(bg$context)[1]
  extenti=rep(0,m);extenti[i]=1;extenti=operator_closure_obj_input(extenti,context)
  extentj=rep(0,m);extentj[j]=1;extentj=operator_closure_obj_input(extentj,context)
  sup=operator_closure_obj_input(pmax(extenti,extentj),context)
  inf=pmin(extenti,extentj)
return(sum(sup-inf))}

attribute_dist=function(i,j,context){object_dist(i,j,context)}

object_dist_mat <- function(context){
  m <- nrow(context)
  ans <- array(0,c(m,m))
  for(k in (1:m)){
	  for(l in (1:m)){
		  ans[k,l]=object_dist(k,l,context)
	  }
 }
	
return(ans)}

attribute_dist_mat <- function(context){
  m <- nrow(context)
  ans <- array(0,c(m,m))
  for(k in (1:m)){
	  for(l in (1:m)){
		  ans[k,l]=attribute_dist(k,l,context)
	  }
 }
	
return(ans)}
		  

  
  
 
 
estimate.concept.lattice.size=function(bg,nrep){    #### Schätzt Anzahl von formalen Begriffen über Monte-Carlo-Simulation
  m=dim(bg$context)[2]
  a=rep(0,nrep)
  for(k in (1:nrep)){
   temp=runif(m)>=0.5
   H=H.attr(temp,bg)
   if(all(H==temp)){a[k]=1}
  }
return(mean(a)*2^m)}


concept.lattice.sample=function(bg,nrep){   #### Zieht zufällig formale Begriff aus formalem Kontext. Achtung: Begriffe sind nicht gleichverteilt
  m=dim(bg$context)[2]
  a=array(0,c(nrep,m))
  for(k in (1:nrep)){
   temp=runif(m)>=0.5
   H=H.attr(temp,bg)
   a[k,]=H
  }
return(a)}
 
 

attr.impl=function(index,bg){### berechnet, was aus {index} folgt
   n=dim(bg$context)[2]
   temp=rep(0,n)
   temp[index]=1
   H=H.attr(temp,bg)
return(which(H==1 & temp!=1))}


random.impl=function(premise.supp,conclusion.supp,bg){
 n=dim(bg$context)[2]
 while(TRUE){
   index=sample((1:n),size=premise.supp ,replace=FALSE)
   temp=attr.impl(index,bg)
   if(length(temp)>=conclusion.supp){return(list(premise=index,conclusion=temp))}
 }
}  




stepsize=5000

cond.print=function(text,step,stepsize){if(stepsize != Inf){if(step %% stepsize ==0 | step==1){print(text)}}}
 
 
#simple.implication.incidence=function(X){  ???
#  m=dim(X)[2]
#  I=array(0,c(m,m));diag(I)=1
#  for(k in (1:m)){
#    for(l in (1:m)){
#      if(all(X[k,]


##########################################




##########################################
########			     	      ########
#######						       #######
######     starshaped sets     ######
#######                            #######
########				          ########
##########################################
						     
						     
starshaped_subgroup_discovery  <- function(Z,u,params=list(Outputflag=0)){#x.train,y.train,x.test,y.test,stylizedBetweenness=sb1,p,VCDim,params=list(outputFlag=0,presolve=0,threads=1),VCcut=TRUE,interval){
  m <- dim(Z)[1]
  M <- list(modelsense="max",obj=u,lb=rep(0,m),ub=rep(1,m))
  solutions <- list()
  objvals <- rep(0,m)
  stars <- array(0,c(m,m))
  for(k in (1:m)){  ## quantify over all starcenters
      M <- modelFromQoset(t(Z[k,,]))
	  M$obj <- u
	  M$lb <- rep(0,m)
	  M$ub <-rep(1,m)
      M$lb[k] <- 1              ## Sternmittelpunkt drinnen
	  M$modelsense <- "max"
	  b <- gurobi(M,params=params)
	  solutions[[k]] <- b
	  objvals[k] <- b$objval
	  stars[k,] <- b$x
	  
	  
	  
  } 
  i <- which.max(objvals) 
return(list(solutions=solutions,objvals=objvals,stars=stars,objval=objvals[i],star=stars[i,]))}
  
  

modelFromQoset <- function(Q){## constructs linear program for the optimization over all upsets of a quasiordered set Q
	
  QQ <- tr(Q)
  m  <- sum(QQ)
  n  <- dim(QQ)[1]
  A  <- array(as.integer(0),c(m,n))
  t  <- 1
  sense <- rep("<=",m)
  for(k in (1:(n-1))){
    for(l in ((k+1):n)){
	   if(QQ[k,l]==1 &QQ[l,k]==0){
	      A[t,k]=1;A[t,l]=-1
		  t=t+1
		}
		
	   if(QQ[k,l]==0 &QQ[l,k]==1){
	      A[t,k]=-1;A[t,l]=1
		  t=t+1
	   }
	   
	   if(QQ[k,l]==1 &QQ[l,k]==1){
	      A[t,k]=1;A[t,l]=-1
		  sense[t]="="
		  t=t+1
		}
	}
  }
  t <- t-1
 ans <- list(A=A[(1:t),],rhs=rep(0,t),sense=sense[(1:t)],lb=rep(0,n),ub=rep(1,n))
return(ans)}  



classification.with.stylized.betweeness=function(x.train,y.train,x.test,y.test,stylizedBetweenness=sb1,p,VCDim,params=list(outputFlag=0,presolve=0,threads=1),VCcut=TRUE,interval){
  
  print(Sys.time())
  m.train <- dim(x.train)[1]
  m.test  <- dim(x.test)[1]
  m       <- m.train+m.test
  labels  <- levels(y.train)
  X       <- rbind(x.train,x.test)
  Y       <- c(y.train,y.test)
  II      <- array(0,c(m,m,m))
  AP     <- array(0,c(m.test,2*m.train));AM=AP
  bnsplus <- bnsminus <- ansplus <- ansminus <- rep(0,m.train)
  ansplussol=list()
  ansminussol=list()
  bnsplussol=list()
  bnsminussol=list()
  sol=list()
  sol2=list()
  t=1
  sols=list()
  
  for(kkk in (1:length(stylizedBetweenness))){
  kkk<<-kkk
  SB <- (stylizedBetweenness[kkk])
  SB <- SB[[1]]
  #Print(SB)
  B       <- SB(X,p=p)
  FI      <- pmin(B$A,B$B)
  FII <<- FI
  
  
  
  for(k in (1:m)){
  
	   if(VCcut){J=incidence.cut(FI[k,,],width=VCDim[kkk],interval=interval)}#c(sort(unique(as.vector(FI[k,,])))[2],1))}
	   else{J=incidence.cut2(FI[k,,],width=VCDim[kkk],interval=c(sort(unique(as.vector(FI[k,,])))[2],1))}
      II[k,,]=pmax(II[k,,],(J))
  }
}

II <<- II
VCDIMS=rep(0,m)
for(kkk in (1:m)){

VCDIMS[kkk]=(width.hopcroft.karp(transitive.hull(II[kkk,,]))$width)}
Print(table(VCDIMS))
  II=CUT(II,EPS,m.train)
  
    II <<- II
  print(Sys.time())
  
  for (ind in (1:m.test)){
    index <- c((1:m.train), ind+m.train)
    #print(Sys.time())
    for(k in (1:m.train)){  ## quant ueber alle sternmittelpunkte## hier auch m moeglich
      M <- modelFromQoset(II[k,index,index])
      M$lb[k] <- 1              ## Sternmittelpunkt drinnen
  
  #1
      v <- rep(0,m.train+1);v[(1:m.train)]=probabilityDifferences(y.train,label=labels[1])
      M$modelsense <- "max"
      M$lb[m.train+1] <- 1   ## testpunkt drinnen
      M$obj <- v  #+    CC*rep(-1,length(v))###fuer  vortrag
      b <- gurobi(M,params=params)
      ansplus[k] <- b$objval
	  ansplussol[[k]]=b$x
	  
	  sols[[t]]=b$x
	  t=t+1
	  
	  ##fuer vortrag:
	  
	  #if(k==K){
	  #b <<- b
	  #}
  
  
  #2
    
	  v <- rep(0,m.train+1);v[(1:m.train)]=probabilityDifferences(y.train,label=labels[2])
      M$obj <- v
      b <- gurobi(M,params=params)
      ansminus[k] <- b$objval
		ansminussol[[k]]=b$x
		
		sols[[t]]=b$x
	  t=t+1
		
  
  #3  
      v <- rep(0,m.train+1);v[(1:m.train)]=probabilityDifferences(y.train,label=labels[1])
      M$obj <- v  
      M$lb[m.train+1] <- 0;M$ub[m.train+1] <- 0  ### testpunkt nicht drinnen
      M$modelsense <- "min"
      b <- gurobi(M,params=params)
      if(is.null(b$objval)){print("warning: no feasible solution")}
   
      if(!is.null(b$objval)){bnsplus[k]=-b$objval}
		bnsplussol[[k]]=b$x
		
		sols[[t]]=b$x
	  t=t+1
	  
	  
  
  #4
      v <- rep(0,m.train+1);v[(1:m.train)]=probabilityDifferences(y.train,label=labels[2])
      M$obj <- v
      b <- gurobi(M,params=params)
      if(is.null(b$objval)){print("warning: no feasible solution")}
      if(!is.null(b$objval)){bnsminus[k]=-b$objval}
	  bnsminussol[[k]]=b$x
  
  sols[[t]]=b$x
	  t=t+1
    }
  
    AP[ind,] <- c(ansplus,bnsplus)
    AM[ind,] <- c(ansminus,bnsminus)
 
  }
  predictions <- factor(rep(y.train[1],m.test),level=labels)
  unique=rep(0,m.test)
  for(k in (1:m.test)){
    if(AP[k,] %glex% AM[k,]){predictions[k] <- labels[1];sol[[k]]=ansplussol[[k]];sol2[[k]]=bnsplussol[[k]]}
    else{predictions[k] <- labels[2];sol[[k]]=ansminussol[[k]];sol2[[k]]=bnsminussol[[k]]}
	if(max(AP[k,]) > max(AM[k,]) | max(AP[k,]) < max(AM[k,])){unique[k]=1}
  }
   
return(list(AP=AP,AM=AM,predictions=predictions,errorProb=mean(y.test!=predictions),unique=unique, unique.prop=mean(unique),betweenProb=betweennessProb(II[(1:m.train),(1:m.train),(1:m.train)],y.train),sol=sol,sol2=sol2,sols=sols))}


cwsb=classification.with.stylized.betweeness


###### stilisierte Zwischenrelationen


sb1=function(XR,p){
  m=dim(XR)[1]
  n=dim(XR)[2]
  A=array(as.integer(0),c(m,m,m))
  B=A
  C=A
  D=as.matrix(dist(XR,method="minkowski",upper=TRUE,p=p))
  MAXD=max(D)#Q=quantile(D,QQ)
  
  for(K in (1:m)){#(1:(m-2))){
  for(L in (1:m)){#((K+1):(m-1))){
  for(M in (1:m)){#((L+1):m)){
   #A[K,L,M]=max(0,D[L,K]-D[M,K],D[L,M]-D[K,M])
   A[K,L,M]=sum(D[K,M])/(sum(D[K,L]+D[L,M]))
   B[K,L,M]=(D[K,L]<D[K,M])#*D[K,M]/MAXD#<=Q
   
   #temp=sign((XR[L,]-XR[K,])*(XR[M,]-XR[K,]))
   #temp2=abs(XR[L,]-XR[K,]) < abs(XR[M,]-XR[K,])
   #i=which(temp>=0 &temp2)
   #A[K,L,M]=length(i)
   #B[K,L,M]=sum(abs(temp[i]))
   
   }}}
   for(K in (1:m)){
   diag(A[K,,])=1
   diag(B[K,,])=1}
 return(list(A=A,B=B))}

##################################################################
##################################################################
################                                 #################
###############     Data Depth in FCA             ################  
################                                 #################
##################################################################



# certain depth functions:



star_depth <- function(context, index_modus){    ## computes a simple depth function by counting how many points are between a given point and a center (index_modus)

# This depth function is not quasiconcave but star-haped if the context is complemented (is this assumption needed? NO!)
  m <- nrow(context)
  ans <- rep(0,m)
  for(k in (1:m)){
     extent <- rep(0,m)
     extent[index_modus] <- 1
     extent[k] <- 1
     extent <- operator_closure_obj_input(extent,context)
     ans[k] <- sum(extent) 

  }
return(m-ans)
}


star_depth2 <- function(context, index_modus){ ## computes a another simple depth function adding for every point to all other points between this point and a center a one 

# This depth function is not quasiconcave but star-haped if the context is complemented (is this assumption needed? NO!)

   m <- nrow(context)
   ans <- rep(0,m)
   for(k in (1:m)){
     extent <- rep(0,m)
     extent[index_modus] <- 1
     extent[k] <- 1
     extent <- operator_closure_obj_input(extent,context)
     ans[which(extent==1)]=ans[which(extent==1)]+1
   }
return(ans)
}
						     
						     
# properties of depth functions	
						     
is_quasiconcave <- function(depths, context){
	
	m <- nrow(context)
	for(k in (1:m)){
		i <- which(depths > depths[k])
		extent <- rep(0,m);extent[i] <- 1
		if(operator_closure_obj_input(extent,context)[k]==1){return(FALSE)}
	}
return(TRUE)
	
}
						     
				
is_strictly_quasiconcave <- function(depths, context){
	
	m <- nrow(context)
	for(k in (1:m)){
		i <- which(depths >= depths[k])
		i[k] <- 0
		extent <- rep(0,m);extent[i] <- 1
		if(operator_closure_obj_input(extent,context)[k]==1){return(FALSE)}
	}
return(TRUE)
	
}
						     
strictly_quasiconcave_pseudohull <- function(depths, context){
	
	m <- nrow(context)
	ans <- depths
	for(k in (1:m)){
		i <- which(depths >= depths[k])
		i[k] <- 0
		extent <- rep(0,m);extent[i] <- 1
		if(operator_closure_obj_input(extent,context)[k]==1){ans[k] <- ans[k]+1/100/m}
	}
return(ans)
	
}	
						     

						     
						     
### depth functions in the context of poset-data
						     
						     
Tukeys_true_median_order <- function(orders,startorder=orders[[1]]*0){   ## coputes that partial order in the space of ALL partial orders that has the maximal tukeys depth wr.t. the given data cloud representet by th given contetxt (given in the form of a list of posets, where every etry of the list is an incidence relation apposited with its negation (In terms of conceptual scaling we use here the complemented scaling
	
 m <- length(orders)
 q <- nrow(orders[[1]])
 W=Reduce('+',orders)
 ans_old <- ans_new <- startorder#orders[[1]]*0#array(0,dim(orders[[1]]))
 
 while(TRUE){
    w <- max(W[which(ans_old==0)])
    i <- which(ans_old==0 & W==w)
    i <- sample(rep(i,2),size=1)	
    ans_new <- ans_old
    ans_new[i] <- 1
    if(! is_extendable_to_partial_order(ans_new)){
	ans_old <<- ans_old
	ans_new <<- ans_new
	#return(ans_old)}
	 
	return(cbind(ans_old[,(1:q)],1-ans_old[,(1:q)]))}
	M1 <- ans_new[,(1:q)]
	diag(M1) <- 1
	M1 <- relation_incidence(transitive_closure(as.relation(M1)))
	M2 <- ans_new[,-(1:q)]	
        ans_old <- cbind(M1,M2)#relation_incidence(transitive_closure(as.relation(ans_new[,(1:q)]))),ans_new[,-(1:q)])
    }
}

Tukeys_true_median_difference <- function(orders1,orders2){   ## coputes that partial order in the space of ALL partial orders that has the maximal tukeys depth wr.t. the given data cloud representet by th given contetxt (given in the form of a list of posets, where every etry of the list is an incidence relation apposited with its negation (In terms of conceptual scaling we use here the complemented scaling
	
 m <- length(orders1)
 q <- nrow(orders1[[1]])
 W1 <- Reduce('+',orders1)
 W2 <-  Reduce('+',orders2)
 W <- pmax(W1,W2)
	W_min <- pmin(W1,W2)
	
	
 W <<- W
 ans_old <- ans_new <- orders1[[1]]*0#array(0,dim(orders[[1]]))
 w  <- max(W[which(ans_old==0)])
 i <- which(ans_old==0 & W==w)
 i <- sample(rep(i,2),size=1)
 while(TRUE){
	 w <<- w
    w_old <- w
	 i_old <- i
    w <- max(W[which(ans_old==0)])
	 ans_old <<- ans_old
	 w <<- w
	 W <<- W
    i <- which(ans_old==0 & W==w)
    i <- sample(rep(i,2),size=1)	
    ans_new <- ans_old
    ans_new[i] <- 1
    if(! is_extendable_to_partial_order(ans_new)){
	ans_old <<- ans_old
	ans_new <<- ans_new
	return(w_old +0.0001*w)}
	M1 <- ans_new[,(1:q)]
	diag(M1) <- 1
	M1 <- relation_incidence(transitive_closure(as.relation(M1)))
	M2 <- ans_new[,-(1:q)]	
        ans_old <- cbind(M1,M2)#relation_incidence(transitive_closure(as.relation(ans_new[,(1:q)]))),ans_new[,-(1:q)])
	w_new <- w
    }
}

Tukeys_geodetic_median_order <- function(corders, proportion,auto=FALSE,fraction=0.75){
	context <- list_to_context(corders)
	TD <- Tukeys_depth(context)
	if(auto){
		TM <- as.vector(Tukeys_true_median_order(corders))
		OTD <- sort(TD,decreasing=TRUE)
		for(k in (1:length(corders))){
			extent <- rep(0,ncol(context))
			extent[which(TD>=OTD[k])]=1
			intent <- calculate_psi(extent,context)
			if(all(intent<=TM)){proportion=k/length(corders)*fraction;break}
		}
	}
	
	i <- which(TD>=quantile(TD,1-proportion))
	extent <- rep(0, length(corders))
	extent[i] <- 1
	intent <- calculate_psi(extent, context)
	dim(intent) <- dim(corders[[1]])
	return(Tukeys_true_median_order(orders=corders,startorder = intent))

	
	
}

is_extendable_to_partial_order <- function( complemented_order ){

  q <- dim(complemented_order)[1]
  M1 <-  relation_incidence(transitive_closure(as.relation(complemented_order[,(1:q)])))
  diag(M1) <- 1
  M2 <-  complemented_order[,-(1:q)]
  if(any(M1==1 & M2 ==1)){return(FALSE)}
  if(!relation_is_acyclic(as.relation(M1))){return(FALSE)}
return(TRUE)}
						  
test_Tukeys_true_median_order <- function(){
	q <- sample((3:5),size=1)
	a <- all_partial_orders(q,complemented=FALSE)
	orders <- list()
	m <- nrow(a)
	for(k in (1:m)){temp <- a[k,];dim(temp) <- c(q,q);orders[[k]] <- cbind(temp,1-temp)}
	i <- sample((1:m),size=ceiling(nrow(a)/3))
	a <- cbind(a,1-a)
	ans1 <- Tukeys_true_median_order(orders[i])
	TD <- Tukeys_depth(rbind(a[i,],a),weights=c(rep(1,length(i)),rep(0,m)))
	j <- which(TD==max(TD))
	for(jj in j){
	ans2 <- (rbind(a[i,],a))[jj,];dim(ans2) <- c(q,2*q)
	ans1 <<- ans1
	ans2 <<- ans2
	if(all(ans1==ans2)){return(TRUE)}
	}	
	return(FALSE)
}
	
