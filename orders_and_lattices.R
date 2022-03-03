library(Matrix)
library(gurobi)
library(igraph)  
library(Biobase) ##für Funktion rowMin
library(geometry) ## für Fufnktion cart2bar (für Erstellung Kontext für Geometrie)



###################################
########				   ########
#######						#######
######     Ordnungstheorie   ######
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
######     Formale Begriffsanalyse  ######
#######                            #######
########				          ########
##########################################

next_closure=function(cop,context,stepsize,n=dim(context)[2],Nmax=700000){   # Next closure Algorithmus zur Berechnung aller Huellen eines gegebenen Hüllenoperators cop vgl. z.B. Ganter. Diskrete Mathematik: geordnete Mengen S.86
  A=rep(0,n)
  A=cop(A,bg)
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
  cond.print(t,step=t,stepsize=bg$stepsize)
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

H.attr=function(A,bg){PSI(PHI(A,context),context)} ## Berechnet zu Merkmalsmenge A (gegeben durch A[i]=1 iff Merkmal i ist in Menge A, 0 sonst) deren Hülle PSI(PHI(A))
	H.obj=function(A,bg){PHI(PSI(A,context),context)} ## Berechnet zu Gegenstandsmenge A (gegeben durch A[i]=1 iff Gegenstand i ist in Menge A, 0 sonst) deren Hülle PHI(PSI(A))
	
implications=function(bg){               ### Hier stimmt was nicht!!!
  a=next.closure(L.infty,bg)
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
   ans$intents=next.closure(H.attr,context,stepsize=stepsize)
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
######     Begriffliches Skalieren  ######
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
##### Optimierung auf Hüllensystemen #####
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


min_k_obj_generated=function(extent,intent,X){min_k.attr_generated(intent,extent,t(X))} # Berecchnet für Begriff gegeben durch Umfang extent und Inhalt intent das maximale k, für das der Begriff k-MGegenstandserzeugt ist (Kontext X muss ebenfalls mit übergeben werden)
  
  
 








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
	 ans$start=c(temp$solution,PSI(temp$solution,list(context=X)))
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



local_object_VCdims=function(X,indexs=(1:dim(X)[1]),outputflag,timelimit,pool=FALSE,transpose=TRUE,additional.constraint=TRUE){
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
	  temp=extent.VC(t(X),additional.constraint=additional.constraint)
      temp$lb[k+n]=1
	}
	else{
	temp=extent.VC((X))
    temp$lb[k]=1
	}
	
    
    if(pool){a=gurobi(temp,list(outputflag=outputflag,timelimit=timelimit,PoolSolutions=100000000,PoolSearchMode=2,Poolgap=0.00001))}
	else{a=gurobi(temp,list(outputflag=outputflag,timelimit=timelimit))}
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

object.dist=function(i,j,bg){
  m=dim(bg$context)[1]
  extenti=rep(0,m);extenti[i]=1;extenti=H.obj(extenti,bg)
  extentj=rep(0,m);extentj[j]=1;extentj=H.obj(extentj,bg)
  sup=H.obj(pmax(extenti,extentj),bg)
  inf=pmin(extenti,extentj)
return(sum(sup-inf))}
attribute.dist=function(i,j,bg){object.dist(i,j,bg=list(context=t(bg$context)))}
  
  
 
 
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
######     Sternfoermige Mengen     ######
#######                            #######
########				          ########
##########################################


starshaped.subgroup.discovery=function(Z,u,params=list(Outputflag=0)){#x.train,y.train,x.test,y.test,stylizedBetweenness=sb1,p,VCDim,params=list(outputFlag=0,presolve=0,threads=1),VCcut=TRUE,interval){
  m=dim(Z)[1]
  M=list(modelsense="max",obj=u,lb=rep(0,m),ub=rep(1,m))
  solutions=list()
  objvals=rep(0,m)
  stars=array(0,c(m,m))
  for(k in (1:m)){  ## quant ueber alle sternmittelpunkte
      M <- modelFromQoset(t(Z[k,,]))
	  M$obj=u
	  M$lb=rep(0,m)
	  M$ub=rep(1,m)
      M$lb[k] <- 1              ## Sternmittelpunkt drinnen
	  M$modelsense="max"
	  b <- gurobi(M,params=params)
	  solutions[[k]]=b
	  objvals[k]=b$objval
	  stars[k,]=b$x
	  
	  
	  
  } 
  i=which.max(objvals) 
return(list(solutions=solutions,objvals=objvals,stars=stars,objval=objvals[i],star=stars[i,]))}
  
  

modelFromQoset=function(Q){## erstellt Lineares Programmierungsproblem zur Optimierung ueber alle Oberhalbmengen einer quasigeordneter Menge Q
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

########################							#####################################################################################
########################							#####################################################################################
########################			HANNAHS TEIL			#####################################################################################
########################							#####################################################################################
########################							#####################################################################################
########################							#####################################################################################


################################################################################
# Formal Concept Analysis and Implications (general)
################################################################################
################################################################################
# FCA - Calculating of all formal concepts based on a formal context given by a 
# cross tabel / incidence
################################################################################
calculate_phi <- function(subset_attributes, context) {
  # Calculates for a subset of attributes the minimal extent based on the given context
  
  # Input: subset_attributes (array): set of attributes
  #         context (matrix): formal context which is used to calculate the extent
  
  # Output: subset (array): the smallest extent (set of objects) in the FCA 
  #                         based on subset_attributes and the formalc context
  
  # Determines and subsets the attributes which are selected
  index_attribute <- which(subset_attributes == 1)
  selected_attributes <- as.matrix(context[ ,index_attribute])
  dim(selected_attributes) <- c(dim(context)[1], length(index_attribute))
  
  # Counting for each object how many selected attributes hold and choosing the
  # one where all attributes are true
  count_objects_attribute_hold <- rowSums(selected_attributes)
  index_obejct <- which(count_objects_attribute_hold == length(index_attribute))
  
  # returning a list which represents which objects correspond to the considered
  # attribute set
  extend <- rep(0,dim(context)[1])
  extend[index_obejct] <- 1
  
  return(extend)
}


calculate_psi <- function(subset_objects, context) {
  # Calculates for a subset of objects the minimal intent based on the given context
  
  # Input: subset_objects (array): set of objects
  #         context (matrix): formal context which is used to calculate the intent
  
  # Output: subset (array): to smallest intent (set of attributes) in the FCA 
  #                         based on subset_objects and context
  
  # Determines and sub-setting the objects which are selected
  index_object <- which(subset_objects == 1)
  selected_objects <- as.matrix(context[index_object,])
  dim(selected_objects) <- c(length(index_object),dim(context)[2])
  
  # Counting for each attribute how many selected objects are related and chose 
  # the ones where all objects are related
  count_attributes_object_related <- colSums(selected_objects)
  index_attribute <- which(count_attributes_object_related == length(index_object))
  
  # returning an array which represents the attributes which correspond to the
  # considered object set
  intent <- rep(0,dim(context)[2])
  intent[index_attribute] <- 1
  return(intent)
}


operator_closure_attr_input <- function(subset_attribute, context){
  # Defines the closure operator for computing all intents (attribute)
  
  # Input: subset_attribute (array): set of attributes
  #         context (matrix): formal context which is used to calculate the intent
  
  # Output: subset (array): to smallest closure in the FCA based on 
  #                         subset_attribute and context
  
  calculate_psi(calculate_phi(subset_attribute, context), context)
} 


operator_closure_obj_input <- function(subset_object, context) {
  # Defines the closure operator for computing all extends (objects)
  
  # Input: subset_object (array): set of objects
  #         context (matrix): formal context which is used to calculate the extent
  
  # Output: subset (array): to smallest closure in the FCA based on 
  #                         subset_object and context
  calculate_phi(calculate_psi(subset_object, context), context)
}


# Auxiliary functions of compute_all_closure, for algorithm-step 2: next closure
adds_element <- function(old_subset, element) { 
  # Adds a further element to old_subset and deletes all larger elements
  # based on: Granter (2013), Diskrete Mathematik: Geordnete Mengen, Springer Spektur, p.85
  
  # input: old_subset (array with 0,1 elements): subset to which the element should be added
  #                                             (1 represents element in subset)
  #         element (integer): element (position) which is added
  
  # output: subset (array with 0,1 elements): subset with added element
  #                                          (1 represents element in subset)
  
  # if the element is the first, the subset only consists of this element
  if (element == 1) {
    subset <- rep(0, length(old_subset))
    subset[element] <- 1
  }
  else {
    index_lower_element_index <- rep(0,length(old_subset))
    index_lower_element_index[(1:(element - 1))] <- 1
    # pmin: A and temp are compared by element by element and the minimum is selected
    subset <- pmin(old_subset, index_lower_element_index)
    subset[element] <- 1
  }
  return(subset)
}


# Auxiliary function of compute_all_closure defining order structure given by 'lektisch' order
compare_closures_lower_i <- function(old_closure, new_closure, element) {
  # Tests if the old_closure is smaller than  the new_closure within the meaning of 
  # 'lektisch' order
  # based on: Granter (2013), Diskrete Mathematik: Geordnete Mengen, Springer Spekturm, p.26 + 84
  
  # Input: old_closure (array with 0,1 elements): closure (subset, 1= element within closure)
  #         new_closure (array with 0,1 elements): closure (subset, 1= element within closure)
  #         element (integer): element which is used for comparing
  
  # Output (logical): returns true if old_closure < new_closure
  if (element == 1) {
    return(new_closure[element] == 1 & old_closure[element] == 0)
  }
  else{
    temp <- rep(0,length(old_closure))
    temp[(1:(element - 1))] <- 1
    return(new_closure[element] == 1 & old_closure[element] == 0 & all(pmin(old_closure,temp) == pmin(new_closure,temp)))
  }
}


# main functions
compute_all_closure <- function(closure_operator, context,
                                number_attributes = NA,
                                already_computed_closures = 1000) {
  # Calculation of all sets of the complete lattice.
  # based on: Granter (2013), Diskrete Mathematik: Geordnete Mengen, Springer Spekturm, p.68
  
  # Input: closure_operator (func): set-operator which calculates the smallest closure
  #               based on a subset
  #         context (matrix): formal context which precises the closure_operator
  #         number_attributes (NA or integer): determines the number of attributes
  #         already_computed_closures (int): states the frequency how often the
  #               information 'how many closures are already computed' is printed 
  
  # Output: (array, elements in 0,1): each row states one computed closure 
  #                                   (1 = element in closure)
  
  
  
  if (is.na(number_attributes)) {
    number_attributes <- dim(context)[2]
  }
  
  # Calculating the first lattice set based on the empty set and the used context
  # Ganter, p68 Algorithm: First Closure
  old_closure <- closure_operator(rep(0, number_attributes), context)
  all_closure <- list()
  all_closure[[1]] <- old_closure
  
  # In this part all further lattice sets are computed
  t <- 2
  not_all_closures_computed <- TRUE
  while (not_all_closures_computed) {
    attributs_selected <- which(old_closure == 1)
    
    # Determining all the attributes which could be added, hence which are not
    # selected yet
    if (length(attributs_selected) == 0) {
      index <- (1:number_attributes)
    }
    else {
      index <- (1:number_attributes)[-attributs_selected]
    }
    
    # Ganter, p.86 Algorithm: Next Closure
    # Going from the larges to the lowest not yet added attribute until the new 
    # calculated closure is larger (in sense of the 'lektisch' order, see Ganter p. 26)
    for (element in sort(index, decreasing = TRUE)) {
      # Adding the new element with 'adds_element()' and computing the closure
      new_closure <- closure_operator(adds_element(old_closure, element), context)
      # Test if the new closer is larger then the older closure. If yes, go on.
      if (compare_closures_lower_i(old_closure, new_closure, element)) {
        break # break of the for-loop (not while)
      }
    }
    
    # Saving the new closure and now it takes the place of the old closure.
    old_closure <- all_closure[[t]] <- new_closure
    
    # Testing if all closures are computed, the last one has all attributes selected
    if (all(new_closure == 1)) {
      not_all_closures_computed <- FALSE
    }
    # Test if print-information on how many closures are already computed
    if (t %% already_computed_closures == 0) {
      cat(t, "many closures were computed.\n")
    }
    # assignment to the new saving space
    t <- t + 1
  }
  # Convert from list to array and return the object
  return(t(array(unlist(all_closure), dim = c(number_attributes, t - 1))))  
}


calculate_concept_lattice <- function(context, compute_extents = TRUE){
  # Calculates the formal concept lattice.
  # Therefore, all formal concept which are defined by the formal context are 
  # calculated.
  
  # Input: context (matrix): represents the formal context (rows: objects, columns: attributes)
  #         compute.extends (logical): If it is sufficient to only calculate the intent
  
  # Output: (list) intents(array (0,1 values)): each row represents one intent, (1 = attribute is contained)
  #                 extent(array with 0,1 values): each row represents one extent, (1 = attribute is contained)
  #                 concepts(list): corresponding intent and extend are saved together
  #                                   saving not by index, but directly by their names
  
  
  result <- list()
  
  # Calculating all intents using the closure operator property
  result$intents <- compute_all_closure(operator_closure_attr_input, context)
  
  number_closure <- dim(result$intents)[1]
  number_objects <- dim(context)[1]
  result$concepts <- rep("", number_closure)
  
  if (compute_extents) { 
    result$extents <- matrix(FALSE, ncol = number_objects, nrow = number_closure)
    for (k in (1:number_closure)) {
      # Calculate the extends based on the intents
      result$extents[k,] <- calculate_phi(result$intents[k,], context)
      result$concepts[k] <- paste("{",
                                  paste((rownames(context))[which(result$extents[k,] == 1)],collapse = ","),
                                  "}   {",
                                  paste((colnames(context))[which(result$intents[k,] == 1)] ,collapse = ","),
                                  "}",
                                  collapse = "")
    }
  }
  else{
    for (k in (1:number_closure)) {
      result$concepts[k] <- paste("{",
                                  paste((colnames(context))[which(result$intents[k,] == 1)],collapse = ","),
                                  "}",
                                  collapse = "")
    }
  }
  
  return(result)
}


################################################################################
# Order Theory - Calculation of a subconceptrelation based on the closure system
# (here: extends)
################################################################################

calculate_incidence <- function(extent_list){  
  # generates incidence matrix of a given data table (here it's a closure set)
  # Needed to plot "Begriffsverband"
  
  # Input: extend_list (matrix): rows represent each object, columns each set
  #                              entry 1: object is in set / entry 0: is not in set
  
  # Output: subconceptrelations (quadratic matrix, logical): the number of rows 
  #         (resp. columns) is the number of sets
  #         entry(i,j) TRUE if i is within j (definition: empty set is within everything)
  
  number_extends <- dim(extent_list)[1]
  
  # Defining memory space
  ans <- matrix(FALSE, ncol = number_extends, nrow = number_extends)
  
  for (k in (1:number_extends)) {
    for (l in (1:number_extends)) {
      # If every element in set k is also in set l, we switch this entry to TRUE
      ans[k,l] <- all(extent_list[k,] <= extent_list[l,])
    }
  }
  return(ans)
}




################################################################################
# Test if subset is a generator
################################################################################

test_if_generator <- function(subset, formal_context, trivial_not_ok = FALSE) {
  
  # This function test if a subset is a generator within the formal context or
  # not. We assume that every object has an attribute
  
  # @subset (vector of (0,1)): 1 represents that the point is within the 
  #                             subset
  # @formal_context (data.frame): crosstable representing the formal context
  #                               number of rows is identical to length of subset
  # @trivial_ok (logical): if trivial generators, where the conclusion equals the
  #                         conclusion should also be printed
  
  # Output (logical): TRUE if the subset is a generator
  
  # The empty set is a generator
  if (sum(subset) == 0) {
    return(TRUE)
  }
  
  # We have to test if each observation in subset as an attribute which distinguishes
  # it self from the rest of the subset
  
  # filter the rows of the subset
  formal_con_red_obj <- formal_context[which(subset == 1), ]
  
  # if only one point is in the subset, it is sufficient if a
  # further object has this attribute 
  if (sum(subset) == 1) {
    has_attr_index <- which(formal_con_red_obj == 1)
    attr_fc_reduced_rowSums <- sum(formal_context[, has_attr_index])
    
    if (!trivial_not_ok) {
      return(TRUE)
    }
    return(any(attr_fc_reduced_rowSums > 1)) # (if generators are not trivial)
  }
  
  
  
  # Now we sum up the columns of the reduced formal context. Each observation needs
  # an attribute which does not hold for itself but for every other attribute in 
  # the subset. Thus, if there exists no, with colSums being identical to 
  # sum(subset)-1, it cannot be a generator
  if (all(!(colSums(formal_con_red_obj) == (sum(subset) - 1)))) {
    return(FALSE)
  }
  
  # we select each attribute which distinguishes the observations
  attr_distinguish <- which(colSums(formal_con_red_obj) == (sum(subset) - 1))
  formal_con_red_obj_attr <- formal_con_red_obj[, attr_distinguish]
  
  # each row must now have an attribute which distinguishes itself, else it
  # is not a generator
  has_obj_distinguish_attr <- list()
  if (is.vector(formal_con_red_obj_attr)) {
    has_obj_distinguish_attr <- which(formal_con_red_obj < length(attr_distinguish))
  }
  if (!is.vector(formal_con_red_obj_attr)) {
    has_obj_distinguish_attr <- which(rowSums(formal_con_red_obj_attr) < length(attr_distinguish))
  }
  
  is_generator <- (length(has_obj_distinguish_attr) == sum(subset))
  
  # We have to test if there exists an attribute which holds for every element 
  # and also for some outside of the subset if we want to exculde trivial generators
  if (is_generator & trivial_not_ok) {
    # if no attribute holds for every object in the subset. The closure of this
    # subset is the entire set and thus it is a generator. Else:
    if (any(colSums(formal_con_red_obj) == sum(subset))) {
      attribute_hold <- which(colSums(formal_con_red_obj) == sum(subset))
      # if any attribute does hold only for the subset, this is not an generator
      if (any(colSums(formal_context[, attribute_hold]) == sum(subset))) {
        is_generator <- FALSE
      }
    } 
  }
  
  return(is_generator)
}

################################################################################
# Sampling random closures, assuming that larger closures have more generators
################################################################################
calculate_prob_depend_size <- function(size, number_obj) {
  # This function calculates the probability of the subset size 
  
  # @size (integer): size of the subset
  # @number_obj (integer): number of elements from which the subset is sampled
  
  # Output (numeric between [0,1]): probability
  
  
  prob <- NA
  if (identical(size %% 2, 0)) { # size is even
    prob <- 2^(-number_obj) * choose(number_obj, floor((number_obj + 1) / 2) + size / 2)
  } else {
    prob <- 2^(-number_obj) * choose(number_obj, floor((number_obj + 1) / 2) - ceiling(size / 2))
  }
  return(prob)
}


calculate_shift_prob <- function(size, number_obj) {
  # This function calculates the probability that we are sampling a subset of
  # of size "size"
  
  # @size (integer): size of the subset
  # @number_obj (integer): entire set size
  
  # Output (numeric between [0,1]): probability
  
  return(choose(number_obj, size)^{-1} * calculate_prob_depend_size(size, number_obj))
}


calculate_rejection_prob <- function(generator_list, closure_size, entire_set_size) {
  
  # This function calculates the rejection probability used in sample_closure.
  # It is based on calculate_shift_prob() and on the set of generator of the 
  # closure sampled
  
  # @generator_list (list): list of generators
  # @closure_size (integer): cardinality of the closure
  # @entire_set_size (integer): cardinality of the set 
  
  # Output (numeric in [0,1]): rejection probability
  
  # Infimum of all generators
  infimum_set <- as.integer(Reduce( "&", generator_list))
  index_infimum <- which(infimum_set == 1)
  size_infimum_set <- sum(infimum_set)
  
  # Computing the probability that one of the sets containing the infimum  and
  # being the subsample of the closure is sampled
  prob_supset_inf <- 0
  for (k in seq(from = 0, to = (closure_size - size_infimum_set))) {
    prob_supset_inf <- prob_supset_inf + choose((closure_size - size_infimum_set), k ) * 
      calculate_shift_prob(size_infimum_set + k, entire_set_size)
  }
  
  # deleting all the probability of the subsets which are not a generator but 
  # contain the infimum
  prob_between <- 0
  if (length(generator_list) > 1) {
    # Computing all sets which are a proper subset of one set in generator_list 
    # and a superset of infimum
    sets_between <- list(infimum_set)
    for (gen in generator_list) {
      element_differ <- as.integer(as.integer(gen | infimum_set) & gen)
      index_element_differ <- which(element_differ == 1)
      
      # we only want proper subsets of gen and since infimum set is already saved 
      # we have >1
      max_add_elements <- length(index_element_differ)
      if (max_add_elements > 1) {
        index_add_elements <- lapply(1:(max_add_elements - 1), 
                                     function(x) combn(max_add_elements, x))
        
        for (add_count in index_add_elements) {
          for (index_add_count in 1:dim(add_count)[2]) {
            index_add <- index_element_differ[add_count[, index_add_count]]
            add_subset <- rep(0, entire_set_size)
            add_subset[index_infimum] <- 1
            add_subset[index_add] <- 1
            
            sets_between <- append(sets_between, add_subset)
          }
          
        }
      }
    }
    
    # deleting redundant rows and transform again
    sets_between <- unique(t(matrix(unlist(sets_between), nrow = entire_set_size)))
    rowsum_set_between <- rowSums(sets_between)
    
    # calculating the probability for these subsets
    for (row_count in 1:length(rowsum_set_between)) {
      prob_between <- prob_between + calculate_shift_prob(rowsum_set_between[row_count], entire_set_size)
    }
  }
  
  # subtract the not generator probability 
  probality_correct <- prob_supset_inf - prob_between
  
  # computing the rejection probability and return
  return( 1 / (2^(entire_set_size) * probality_correct))
} 


sample_closure <- function(X, number_obj,
                           calculate_closure, list_info_calculate_closure,
                           calculate_generator, list_info_calculate_generator) {
  
  # This is a modified version of the Algorithm 1 given by Ganter (2011).
  # We assume that larger subsets lead to larger closure systems which have
  # a larger set of generating sets.
  
  # Instead of sampling random a subset, we reduce the probability to sample larger
  # ones, since they (under our assumption) have a higher probability of rejection.
  # This imbalance is corrected in the rejection probability
  
  # @X (integer): the number of drawn samples
  # @number_obj (integer): number of elements from which the subset is sampled
  # @calculate_closure (fct): function to calculate the closure of a subset
  # @list_info_calculate_closure: list which is transferred at calculate_closure
  # @calculate_generator (fct): function to calculate the generators of the 
  #                             closure of a subset
  # @list_info_calculate_closure: list which is transferred at calculate_generator
  
  # Output (matrix): each row represent an uniform sampled extent
  
  closure_calculation <- TRUE
  samples_count <- 0
  samples <- matrix(rep(0, X * number_obj), ncol = number_obj)
  
  # The probability of the cardinality of the sets
  prob_size <- calculate_prob_depend_size(size = seq(from = 0, to = number_obj), 
                                          number_obj = number_obj)
  
  while (closure_calculation) {
    
    # sampling the cardinality
    size_subset <- sample(x = seq(from = 0, to = number_obj), size =  1, replace = TRUE, prob = prob_size)
    
    # sampling uniform a set with this cardinality
    subset_index <- sample(seq(from = 1, to = number_obj), size_subset, replace = FALSE)
    subset <- rep(0, number_obj)
    subset[subset_index] <- 1
    
    # calculate the closure and all the generators
    closure <- calculate_closure(subset, list_info_calculate_closure)$conclusion
    generator_list <- calculate_generator(closure, list_info_calculate_generator)
    
    # calculate the rejection probability
    rejection_prop <- calculate_rejection_prob(generator_list, sum(closure), number_obj) 
    
    # use of the rejection probability to obtain uniform drawn samples
    r <- runif(1, min = 0, max = 1)
    if (r <= rejection_prop) {
      samples_count <- samples_count + 1
      samples[samples_count, ] <- closure
      cat("In sample_closure: A closure is sampled. \n")
      if (identical(samples_count, X)) {
        closure_calculation <- FALSE 
      }
    }
    gc() # garbage collection
  }
  
  return(samples)
}




################################################################################
# Merging formal contexts
################################################################################
calculate_conclusion_merged <- function(premise, list_info) {
  
  # This function computes the conclusion of a two merged formal context
  
  # @premise (vector of (0,1)): 1 represents that the point is within the premise
  # @list_info (list): this list contains the needed functions to calculate the
  #                    conclusion of the first and second formal context as well
  #                    as all needed inputs of these functions
  
  # Output (vector of (0,1)): the conclusion of premise based on the merged formal
  #                           context
  
  list_info_1 <- list_info$info_1
  list_info_2 <- list_info$info_2
  calculate_conclusion_1 <- list_info$calculate_conclusion_1
  calculate_conclusion_2 <- list_info$calculate_conclusion_2
  
  # Calculates the conclusion of each single context
  conclusion_1 <- calculate_conclusion_1(premise, list_info_1)$conclusion
  conclusion_2 <- calculate_conclusion_2(premise, list_info_2)$conclusion
  
  # The conclusion of the merged formal context is the intersection of the two 
  # conclusion calculated on the single formal contexts
  return(list(premise = premise, conclusion = as.integer(conclusion_1  & conclusion_2)))
}



calculate_generator_merged <- function(subset, list_info) {
  
  # This function computes the generators of a subset based on two merged formal context
  
  # @subset (vector of (0,1)): 1 represents that the point is within the premise
  # @list_info (list): this list contains the needed functions to calculate the
  #                    conclusion and the generators of the first and second 
  #                    formal context as well as all needed inputs of these functions.
  #                    Further the crosstable of the merged formal context is in list_info.
  
  # Output (list of vectors): all generators of the closure of subset based on 
  #                           the merged formal context

  calculate_generator_1 <- list_info$calculate_generator_1
  calculate_generator_2 <- list_info$calculate_generator_2
  list_info_1 <- list_info$info_1
  list_info_2 <- list_info$info_2
  
  calculate_conclusion_1 <- list_info$calculate_conclusion_1
  calculate_conclusion_2 <- list_info$calculate_conclusion_2
  list_info_conc_1 <- list_info$info_conc_1
  list_info_conc_2 <- list_info$info_conc_2
  
  formal_context_merged <- list_info$formal_context
  
  number_obj <- dim(formal_context_merged)[1]
  
  # Calculate the generators of the single formal context of subset
  generators_1 <- calculate_generator_1(subset = subset,list_info_1)
  generators_2 <- calculate_generator_2(subset = subset, list_info_2)
  
  # Calculate the closure of the subset based on the merged formal context
  closure_subset <- calculate_conclusion_merged(subset, list(info_1 = list_info_conc_1,
                                                              info_2 = list_info_conc_2,
                                                              calculate_conclusion_1 = calculate_conclusion_1,
                                                              calculate_conclusion_2 = calculate_conclusion_2))$conclusion
  
  # Every generator of the merged formal context can be defined as a union of 
  # a generator in the first and in the second context or it corresponds to 
  # a generator of the first/second context.
  generator <- list()
  for (gen_1 in generators_1) {
    for (gen_2 in generators_2) {
      # test if union is generator
      union_generator <- (gen_1 | gen_2) * 1
      if (test_if_generator(union_generator, formal_context_merged, trivial_not_ok = FALSE)) {
        # test if it really produces the same closure
        inner_closure <- calculate_conclusion_merged(union_generator, list(info_1 = list_info_conc_1,
                                                                          info_2 = list_info_conc_2,
                                                                          calculate_conclusion_1 = calculate_conclusion_1,
                                                                          calculate_conclusion_2 = calculate_conclusion_2))$conclusion
        if (identical(inner_closure, closure_subset)) {
          generator <- append(generator, list(union_generator))
        }
      }
    }
  }
  

  for (gen_1 in generators_1) {
    # test if generator
    if (test_if_generator(gen_1, formal_context_merged, trivial_not_ok = FALSE)) {
      # test if it really produces the same closure
      inner_closure <- calculate_conclusion_merged(gen_1, list(info_1 = list_info_conc_1,
                                                               info_2 = list_info_conc_2,
                                                               calculate_conclusion_1 = calculate_conclusion_1,
                                                               calculate_conclusion_2 = calculate_conclusion_2))$conclusion
      if (identical(inner_closure, closure_subset)) {
        generator <- append(generator, list(gen_1))
      }
    }
  }
  

  for (gen_2 in generators_2) {
    # test if generator
    if (test_if_generator(gen_2, formal_context_merged, trivial_not_ok = FALSE)) {
      # test if it really produces the same closure
      inner_closure <- calculate_conclusion_merged(gen_2, list(info_1 = list_info_conc_1,
                                                               info_2 = list_info_conc_2,
                                                               calculate_conclusion_1 = calculate_conclusion_1,
                                                               calculate_conclusion_2 = calculate_conclusion_2))$conclusion
      if (identical(inner_closure, closure_subset)) {
        generator <- append(generator, list(gen_2))
      }
    }
  }
  
  # sometimes the cart2bary function does not work, then no subset is found
  # and this function throws an error, to test if really cart2bary was the 
  # problem we print this
  if (is.null(unlist(generator))) {
    cat("subset:", subset, " and closure:", closure_subset, "\n")
    cat("matrix:", unlist(generator), "\n")
    return(closure_subset)
  }
  
  
  # deleting redundant rows and transform again
  generator <- unique(t(matrix(unlist(generator), nrow = number_obj)))
  generator <- lapply(seq_len(nrow(generator)), function(i) generator[i,])
  
  return(generator)
}



help_parallel_merge_forcont_gufimpl_union <- function(X,
                                                      number_ufg_2, number_obj,
                                                      ufg_impl_1, ufg_impl_2, 
                                                      merged_formal_context) {
  
  # This function is used within merge_forcont_based_gufimpl to parallelize a
  # part of the calculation. For a fixed union--free generic generator of the 
  # first formal context, we merge this one with every union--free generic
  # generator of the second formal context and test if its an generator of the
  # merged formal context.
  
  # @X (integer): count of the used union--free generic generator of the first
  #               formal context
  # @number_ufg_2 (integer): number of implications of the second formal context
  # @number_obj (integer): number of objects
  # @ufg_impl_1 (simple_triplet_matrix): the implications of the first formal context
  # @ufg_impl_2 (simple_triplet_matrix): the implications of the second formal context
  # @merged_formal_context (dataframe): crosstable representing the merged formal context
  
  # Output (list of vectors): list of generators of the merged formal context
  
  generators_i_column <- list()

  for (count_ufg_2 in seq(1, number_ufg_2)) {
    # the generator of the first formal context extracted from ufg_impl_1
    index_row_1 <- which(ufg_impl_1$i == X)
    index_conclusion_based_on_row_1 <- which(ufg_impl_1$v[index_row_1] == 1)
    index_premise_1 <- ufg_impl_1$j[index_row_1][index_conclusion_based_on_row_1]
    size_premise <- length(index_premise_1)
    
    inner_premise_1 <- rep(0, number_obj)
    inner_premise_1[index_premise_1] <- 1
    
    # the generator of the second formal context extracted from ufg_impl_2
    index_row_2 <- which(ufg_impl_2$i == count_ufg_2)
    index_conclusion_based_on_row_2 <- which(ufg_impl_2$v[index_row_2] == 1)
    index_premise_2 <- ufg_impl_2$j[index_row_2][index_conclusion_based_on_row_2]
    size_premise_2 <- length(index_premise_2)
    
    inner_premise_2 <- rep(0, number_obj)
    inner_premise_2[index_premise_2] <- 1
    
    # union of these two premises
    union_premise <- as.integer(inner_premise_1 | inner_premise_2)
    index_union_premise <- which(union_premise == 1)

    # test if union is a generator
    if (test_if_generator(union_premise, merged_formal_context, trivial_not_ok = TRUE)) {
      generators_i_column <- append(generators_i_column, list(index_union_premise))
    }
  }
  
  # delete duplication and return
  duplicated_gen <- duplicated(generators_i_column)
  return(generators_i_column[!duplicated_gen])
}



help_parallel_merge_forcont_gufimpl_conclusion <- function(X,
                                                           number_obj,
                                                           info_concl_merged) {
  
  # This function is used within merge_forcont_based_gufimpl to parallelize the
  # computation of the conclusions. 
  
  # @X (list): the index of the premise 
  # @number_obj (integer): the size of the entire set considered
  # @info_concl_merged (list): the needed information to compute the conclusion
  #                           of a given subset
  
  # Output (list): contains the index of the conclusion and premises, the corresponding
  #                 values and the length of the premises
  
  # Memory 
  j_column <- list()
  v_value <- list()
  length_premise <- list()
  
  # Extract generator of the generator list
  index_gen <- X
  gen <- rep(0, number_obj)
  gen[unlist(index_gen)] <- 1
  
  # calculate conclusion
  inner_conclusion_premise <- calculate_conclusion_merged(gen, info_concl_merged)
  index_inner_premise <- which(inner_conclusion_premise$premise == 1)
  size_inner_premise <- length(index_inner_premise)
  
  inner_conclusion <- inner_conclusion_premise$conclusion
  inner_conclusion[index_inner_premise] <- 0
  
  index_inner_conclusion <- which(inner_conclusion == 1)
  size_inner_conclusion <- length(index_inner_conclusion)
  
  # filter all redundant implications
  if (length(index_inner_conclusion) > 0) {
    # Saving the conclusion
    
    # Note that we do not save these as simple_triplet_matrizes!
   
    j_column <- index_inner_conclusion
    v_value <- rep(-1/size_inner_conclusion, size_inner_conclusion)
    
    
    # Saving premise
    j_column <- append(j_column, index_inner_premise)
    v_value <- append(v_value, rep(1, size_inner_premise))
    
    length_premise <- size_inner_premise
    
    # count_implication <- count_implication + 1
    
  }
  return(list(j_column = j_column, v_value = v_value, length_premise = length_premise))
}



merge_forcont_based_gufimpl <- function(ufg_impl_1, ufg_impl_2,
                                        info_concl_merged,
                                        merged_formal_context, 
                                        cpus = 1) {
  
  # This function defines the family of implication to calculate the stts
  # and vc dimension based on the set of extents given by a merged formal context
  

  # @ufg_impl_1 (simple_triplet_matrix): the implications of the first formal context
  # @ufg_impl_2 (simple_triplet_matrix): the implications of the second formal context
  # @info_concl_merged
  # @merged_formal_context (dataframe): crosstable representing the merged formal context
  # @cpus (integer): number of CPUs used for parallelization
  
  # Output (list): A - describes the family of implications
  #                length_premise - the length of the premise corresponding to the 
  #                                 rows of A
  #               REST - for gurobi calculation
  
  
  
  
  # If ufg_impl_1 or ufg_impl_2 is not a simple_triplet_matrix, only trivial implications
  # are true for this context, thus only trivial implications are true for the
  # merged formal context
  if (!(is.simple_triplet_matrix(ufg_impl_1) && is.simple_triplet_matrix(ufg_impl_2))) {
    number_obj <- dim(as.matrix(ufg_impl_1))[2]
    model <- list(A = array(rep(0, number_obj), dim = c(1,number_obj)),
                   obj = NULL,
                   rhs = NULL,
                   sense = NULL,
                   lb = rep(0, number_obj),
                   ub = rep(1, number_obj),
                   modelsense = NULL,
                   vtypes = rep('B',number_obj),
                   length_premise = c(0))
    return(model)
  }
  
  
  number_obj <- max(ufg_impl_1$j)
  number_ufg_1 <- max(ufg_impl_1$i)
  number_ufg_2 <- max(ufg_impl_2$i)
  
  cat(paste0("In merge_forcont_based_gufimp: Merging two formal contextes with number_ufg_1: ", number_ufg_1, " and  number_ufg_2: ", number_ufg_2,  ".\n"))

  # We begin with computing the set of generators of the merged formal context based
  # on ufg_impl_1 and ufg_impl_2. Each generator of the merged formal context can  
  # be defined as a union of a generator in the first and in the second context  
  # or it corresponds to a generator of the first/second context.
  
  # Now, we compute all unions of the generators given by  ufg_impl_1 and ufg_impl_2
  generators_i_column <- mclapply(X = seq(1, number_ufg_1), 
                                 FUN = help_parallel_merge_forcont_gufimpl_union,
                                 number_ufg_2 = number_ufg_2,
                                 number_obj = number_obj,
                                 ufg_impl_1 = ufg_impl_1, 
                                 ufg_impl_2 = ufg_impl_2, 
                                 merged_formal_context = merged_formal_context,
                                 mc.set.seed = TRUE,
                                 mc.cores = cpus) 
  
  cat("In merge_forcont_based_gufimp: Entire double for loop calculated.\n")
  
  # delete duplicates
  generators_i_column <- unlist(generators_i_column, recursive = FALSE)
  duplicated_gen <- duplicated(generators_i_column)
  generators_i_column <- generators_i_column[!duplicated_gen]
  
  
  
  # going through all generators given by ufg_impl_1 and test if they are generators
  # of the merged formal context
  for (count_ufg_1 in seq(1, number_ufg_1)) {
    # extracting the count_ufg_1 generator of ufg_impl_1 
    index_row <- which(ufg_impl_1$i == count_ufg_1)
    index_conclusion_based_on_row <- which(ufg_impl_1$v[index_row] == 1)
    index_premise <- ufg_impl_1$j[index_row][index_conclusion_based_on_row]
    size_premise <- length(index_premise)
    
    inner_premise <- rep(0, number_obj)
    inner_premise[index_premise] <- 1
    
    # test if generator
    if (test_if_generator(inner_premise, merged_formal_context, trivial_not_ok = TRUE) ) {
      generators_i_column <- append(generators_i_column, list(index_premise))
    }
  }
  cat("In merge_forcont_based_gufimp: Entire second for loop calculated.\n")
  
  
  # going through all generators given by ufg_impl_1 and test if they are generators
  # of the merged formal context
  for (count_ufg_2 in seq(1, number_ufg_2)) {
    # extracting the count_ufg_2 generator of ufg_impl_2
    index_row <- which(ufg_impl_2$i == count_ufg_2)
    index_conclusion_based_on_row <- which(ufg_impl_2$v[index_row] == 1)
    index_premise <- ufg_impl_2$j[index_row][index_conclusion_based_on_row]
    size_premise <- length(index_premise)
    
    inner_premise <- rep(0, number_obj)
    inner_premise[index_premise] <- 1
    
    # test if generator
    if (test_if_generator(inner_premise, merged_formal_context, trivial_not_ok = TRUE)) {
      generators_i_column <- append(generators_i_column, list(index_premise))
    }
  }
  cat("In merge_forcont_based_gufimp: Entire third for loop calculated.\n")
  
  
  
  # delete duplicates
  duplicated_gen <- duplicated(generators_i_column)
  generators_i_column <- generators_i_column[!duplicated_gen]
  cat("In merge_forcont_based_gufimp: all duplications deleted. \n")
  
  
  
  # if there exists no generator, we return an empty family of implications
  if (length(generators_i_column) == 0) {
    model <- list(A = array(rep(0, number_obj), dim = c(1,number_obj)),
                  obj = NULL,
                  rhs = NULL,
                  sense = NULL,
                  lb = rep(0, number_obj),
                  ub = rep(1, number_obj),
                  modelsense = NULL,
                  vtypes = rep('B', number_obj),
                  length_premise = c(0))
    return(model)
  }
  
  # Calculate conclusions of the generators and save both
  column_value <- mclapply(X = generators_i_column,
                           FUN = help_parallel_merge_forcont_gufimpl_conclusion,
                           number_obj = number_obj,
                           info_concl_merged  = info_concl_merged,
                           mc.set.seed = TRUE,
                           mc.cores = cpus)
  cat("In merge_forcont_based_gufimp: All conclusions are calculated.\n")
  
  length_premise <- unlist(lapply(column_value, `[[`, 3))
  j_column <- lapply(column_value, `[[`, 1)
  v_value <- lapply(column_value, `[[`, 2)
  
  
  
  
  i_row <- list()
  row_count <- 1
  for (row_insert in j_column) {
    if (length(row_insert) > 0) {
      i_row <- append(i_row, rep(row_count, length(row_insert)))
      row_count <- row_count + 1
    }
  }

  
  # Starting the garbage collection
  gc()
  
  # if there exists no not trivial implication we return an empty implication matrix 
  if (length(length_premise) == 0) {
    model <- list(A = array(rep(0, number_obj), dim = c(1,number_obj)),
                  obj = NULL,
                  rhs = NULL,
                  sense = NULL,
                  lb = rep(0, number_obj),
                  ub = rep(1, number_obj),
                  modelsense = NULL,
                  vtypes = rep('B', number_obj),
                  length_premise = c(0))
    return(model)
  }
  
  
  
  i_row <- as.array(unlist(i_row))
  j_column <- as.array(unlist(j_column))
  v_value <- as.array(unlist(v_value))
  length_premise <- as.array(unlist(length_premise))

  
  # Construction of the gurobi_model
  model <- list(A = simple_triplet_matrix(i = i_row, j = j_column, v = v_value),
                obj = NULL,
                rhs = NULL,
                sense = NULL,
                lb = rep(0, number_obj),
                ub = rep(1, number_obj),
                modelsense = NULL,
                vtypes = rep('B', number_obj),
                length_premise = length_premise)
  
  return(model)
}







####################################################################################################################################################
