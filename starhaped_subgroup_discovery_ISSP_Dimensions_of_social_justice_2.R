TD <- function(subset,context){



  if(class(subset)=="numeric"){return(1-max(colMeans(context[,which(subset==0)])))}

  ans <- rep(0,nrow(subset))
  for(k in (1:nrow(subset))){ans[k] <- TD(subset[k,],context)}

  return(ans)


}



 ranking_scaling <-function(X,C=Inf,remove.full.columns=TRUE){ ## adaptiert für < anstelle von <=
  m=dim(X)[1]
  n=dim(X)[2]
  NAMES=rep("",n^2)
  ans=array(0,c(m,n^2))
  temp=array(0,c(n,n))
  for(k in (1:m)){
    for(l1 in (1:n)){
      for(l2 in (1:n)){
        temp[l1,l2]=((X[k,l1]  < X[k,l2])  & (X[k,l1] +C >= X[k,l2]) )*1
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








##### read data

library(foreign)

  # Allbus 2014 ISSP
  a <- read.spss("ZA5240_v2-2-0.sav",use.value.labels=FALSE)

  # 4 Dimensions of social justice (Leistungsprinzip, Gleichheitsprinzip, Anrechtsprinzip, Bedarfsprinzip (principle of achievement principle, principle of equality, principle of entitlement, principle of demand))
  # measured by 8 constructs (2 for each dimension)

  # plus as target variable: answer to the question

  #'Do you believe that you will receive your fair share'
  # F055
  # Im Vergleich dazu, wie andere hier in Deutschland leben: Glauben Sie, dass Sie Ihren -
  #   (Int.: Vorgaben bitte vorlesen!)
  # >gerechten Anteil erhalten,
  # >mehr als Ihren gerechten Anteil,
  # >etwas weniger oder
  # >sehr viel weniger?
  #   1 Sehr viel weniger
  # 2 Etwas weniger
  # 3 Gerechten Anteil
  # 4 Mehr als gerechten Anteil
  # 8 Weiß nicht
  # 9 Keine Angabe



  # plus income

  # Only respondents form east Germany are considered (a$V7==1)
  X <- data.frame(a$V217,a$V221,a$V218,a$V223,a$V219,a$V224,a$V220,a$V222,a$V173,a$V417,a$V7)

 i <- which(X[,1] != 0 & X[,2] !=0 & X[,3]!=0 & X[,4]!=0 & X[,5]!=0 & X[,6]!=0 &X[,7]!=0 & X[,8]!=0  &  X[,1] != 9 & X[,2] !=9 & X[,3]!=9 & X[,4]!=9 & X[,5]!=9 & X[,6]!=9 &X[,7]!=9 & X[,8]!=9  & X[,9]!=9  &X[,9]!=8 & !(X[,10] %in% c(99999,99997,0)) & a$V7==1)

 X <- X[i,]


# W <- ranking_scaling(X)

 m <- nrow(X)




 ans <- NULL

 for(k in (1:m)){
 M <- array(1,c(4,4))
 diag(M) <- 0
 for(k1 in (1:4)){
   for(k2 in (1:4)){
      for(l1 in (0:1)){
	    for(l2 in (0:1)){
		 if(X[k,2*k1-1+l1] >= X[k,2*k2-1 +l2]){M[k1,k2]=0}

		 }}}}
		 diag(M) <-1
		 for(i in (1:4)){
   for(j in (1:4)){

     if (M[i,j]==1 & M[j,i]==1){M[i,j]=0; M[j,i]=0}
	 }}

	 diag(M) <- 1
	 colnames(M) <- rownames(M) <- c("achievement", "equality","entitlement", "demand")
		 ans <- rbind (ans,as.vector(M))
		 }


context <- cbind(ans,1-ans)

c_orders <- convert_context_to_list(context,complemented=TRUE,row_names=c("achievement", "equality","entitlement", "demand"),col_names=c("achievement", "equality","entitlement", "demand","achievement", "equality","entitlement", "demand"))

 # compute stylized betweeness relation Z:

 Z <- array(0,rep(length(c_orders),3))


attribute_weights=colMeans(context)
for(k in (1:dim(Z)[1])){
  for(l in (1:dim(Z)[1])){
    for(m in (1:dim(Z)[1])){


      Z[k,l,m] <- stylized_betweeness(context[k,],context[l,],context[m,],context,attribute_weights=attribute_weights) #between(corders[[k]],corders[[l]],corders[[m]])
      #print(Z[k,l,m])
    }
  }
  print(k)


}
# Markierung 1: (Zeile 142)
# ab hier Speicherabbild
#A:

 # target variable: Income
 target <- compute_objective(list(target=(X[,10]>=median(X[,10]))),target="target",target_class="TRUE")
 table(target)
 ans <- starshaped_subgroup_discovery(stylized_betweenness = Z,objective=W$yw,vc_dim=Inf)

 # ans$objval
 # [1] 85.02752

 #  statistical significance

 nrep <- 200
 h0 <- rep(0, nrep)
 for(k in (1:nrep)){h0[k] <- starshaped_subgroup_discovery_h0(ans$models)}

 mean(h0 >= ans$objval)



 ##


 #B:

 # target variable: fair share
 target <- compute_objective(list(target=(X[,9] <= 2)),target="target",target_class="TRUE")
 table(target)
 ans <- starshaped_subgroup_discovery(stylized_betweenness = Z,objective=target,vc_dim=Inf)
 ans <- starshaped_subgroup_discovery(stylized_betweenness = Z,objective=target,vc_dim=10)

# ans$objval
#  [1] 0.1487426

# plot_stars(ans)
# [1]   2  11 248 274 281 433 659 857

# ans$center_id

 #185



 center_order <- c_orders[[185]]
 center_order <- center_order[,(1:4)]
 ddandrda:::plot_order(t(center_order))


 border_points <- c(2,11,248,433,659,857,274,281)
 for(k in (1:length(border_points))){

   M <- (c_orders[[border_points[k]]])[,(1:4)]
   ddandrda:::plot_order(t(M))

 }


 ##





 #  statistical significance

 nrep <- 2000
 h0 <- rep(0, nrep)
 for(k in (1:nrep)){h0[k] <- starshaped_subgroup_discovery_h0(ans$models)

 print(mean(h0[(1:k)] >= ans$objval))
 }

 #gewichtete Variante
 nrep <- 2000
 h0 <- rep(0, nrep)
 for(k in (1:nrep)){
 target =sample(target)
 W=weighted.repr(contextt,target)
h0[k] <- starshaped_subgroup_discovery_recompute(models=ans$models, objective=W$yw)#stylized_betweenness = Z,objective=W$yw,vc_dim=Inf)$objval

 print(mean(h0[(1:k)] >= ans$objval))
 }

 index <- which(ans$star==1)




###############


 # target variable: income
 target <- compute_objective(list(target=(X[,10] >= median(X[,10]))),target="target",target_class="TRUE")
 table(target)
 ans <- starshaped_subgroup_discovery(stylized_betweenness = Z,objective=target,vc_dim=Inf)
 ans <- starshaped_subgroup_discovery(stylized_betweenness = Z,objective=target,vc_dim=10)

## Analyse mit Tiefenfunktionen

idx1 <- which(X[,9]<=1)
idx2 <- which(X[,9]>1)
C1 <- C[idx1,]
C2 <- C[idx2,]
D1 <- TD(C,C1)
D2 <- TD(C,C2)
which.max(D1)
which.max(D2)
i1 <- which.max(D1)
i2 <- which.max(D2)


min(TD(C[i1,],C2)   , TD(C[i2,],C1))



Q <- C[1,(1:16)];dim(Q) <- c(4,4);rownames(Q) <- colnames(Q) <- c("Leistung","Gleichheit","Anrecht","Bedarf");plot(as.relation(Q))

nrep <-1000
  A <- rep(0,nrep)

 for(k in (1:nrep)){


 idx <- sample((1:nrow(C)),size=115)

 C1 <- C[idx,]
 C2 <- C[-idx,]
 D1 <- TD(C,C1)
 D2 <- TD(C,C2)
i1 <- which.max(D1)
i2 <- which.max(D2)

A[k] <- min(TD(C[i1,],C2)   , TD(C[i2,],C1))
print(k)
plot(D1,D2)
 }

