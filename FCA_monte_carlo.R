eins=function(...){1}
zwei=zwei

concept.gen=function(bg,steps=10000,f){
MAX=-Inf
 m=dim(bg$context)[1] 
 n=dim(bg$context)[2] 
 top.attr=H.attr(rep(0,n),bg)#PSI(rep(1,m),bg)
 bottom.obj=H.obj(rep(0,m),bg)#PHI(rep(1,n),bg)
 
 if(runif(1)>0.5){
     A=rep(1,m)
	 B=top.attr
	}
else{
   B=rep(1,n)
   A=bottom.obj
 }
 
 for( i in (1:steps)){
   if(runif(1)>0.5){
      a=sample((1:n),size=1)
	  BB=B; BB[a]=1
	  AA=PHI(BB,bg)
	  BB=PSI(AA,bg)
	  #print("c")
	  #print(B)
	  #print(BB)
	  alpha=G_ext(AA,A,bg)*n/G_int(B,BB,bg)/m
	  if(is.na(alpha)){alpha=0}
	 }
   else{
	o=sample((1:m),size=1)
	AA=A;AA[o]=1
	BB=PSI(AA,bg)
	AA=PHI(BB,bg)
	alpha=G_int(BB,B,bg)*m/G_ext(A,AA,bg)/n
	if(is.na(alpha)){alpha=0}
    }
	#print(alpha)
	if(f(B,bg)>MAX){BMAX=B}
	MAX=max(MAX,f(B,bg))
    if(runif(1)< alpha *f(BB,bg)/f(B,bg)){
       A=AA; B=BB
     }
if(runif(1)>= Q){B=BMAX;A=PHI(B,bg)}}


print(c("alpha",alpha))
return(B)}	
#T=concept.gen(bg,15000,f)

G_int=function(B,BB,bg){
#print(B)
#print(BB)
 if(all(B==BB)){return(0)}
  ans=0
  i=which(BB==1 & B==0)
 # print(i)
  for(k in i ){
    temp=B;temp[k]=1
	if(all(H.attr(temp,bg)==BB)){ans=ans+1}
}
print(c("ans",dim(bg$context),ans))
return(ans)}
	


G_ext=function(A,AA,bg){ G_int(A,AA,list(context=t(bg$context)))}
 
 
 #T=concept.gen(bg,10000,f)
 
 
 g=function(x,bg){
  m=dim(bg$context)[2]
  xx=rep(0,m)
  t=1
  k=1
  T=0
  while(TRUE){
    if(t>m){break}
    while(xx[t]==1 & t<m){t=t+1}
	if(x[t]==0){T=T+1}
	if(x[t]==1){
	T=T+1
	xx[t]=1
	xxx=H.attr(xx,bg)
	MAX <<- max(MAX,sum(xxx*v))
	if(any(xxx[(1:t)]!=xx[(1:t)])){xx[t]=0;T=T-1}
	else{xx=xxx}}
	#print(xx)
	t=t+1
}
return(list(x=xx,K=T))}
	
	
PHI=function(A,bg){
 if(all(A==1)){}
  i=which(A==1)
  temp=as.matrix(bg$context[,i])
  dim(temp)=c(dim(bg$context)[1],length(i))
  S=rowSums(temp)
  j=which(S==length(i))
  ans=rep(0,dim(bg$context)[1])
  ans[j]=1
return(ans)}

#res=CEoptim(H,maximize=TRUE,discrete=list(probs=p0),N=3000,rho=0.01)
mc.concept.count=function(bg,eps,steps){
  m=dim(bg$context)[1]
  t =12*m /eps^2
  r=rep(0,m)
  for(i in(3:m)){
    r[i]=0
    for(k in (1:t)){
       B=concept.gen(bg=list(context=X[(1:i),]),steps=steps,f=eins)
	   if(all(H.attr(B,bg=list(context=X[(1:(i-1)),]))==B)){r[i]=r[i]+1}
	}
	r[i]=r[i]/t
 }
f print(r)
return(prod(1/r[-(1:2)]))}
