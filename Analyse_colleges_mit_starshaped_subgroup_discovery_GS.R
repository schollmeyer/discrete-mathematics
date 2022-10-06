between <- function(p,q,r){all(pmin(p,r) <= q)}

between(corders[[k]],corders[[l]],corders[[m]])


context <- list_to_context(corders)

Z <- array(0,rep(length(corders),3))

for(k in (1:dim(Z)[1])){
  for(l in (1:dim(Z)[1])){
    for(m in (1:dim(Z)[1])){
      
      
      Z[k,l,m] <- stylized_betweeness(context[k,],context[l,],context[m,],context,attribute_weights=colMeans(context)) #between(corders[[k]],corders[[l]],corders[[m]])
      #print(Z[k,l,m])
    }
  }
  print(k)
  
  
}


ans <- starshaped_subgroup_discovery(Z,v,vc_dim=35)
ans$obj