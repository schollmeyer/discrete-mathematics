sample_shatterable_K_objset <- function(context,K,subset=rep(0,nrow(context){
  if(sum(subset)==K){return(subset)}
  extent <- operator_closure_obj_input(subset,context)
  idx <- which(extent==0)
  
  for(k in sample(idx)){
    new_subset <- subset
    new_subset[k] <-1
    if(objset_is_shatterable(new_subset,context){return(new_subset)}
       
    }
    
    return(NULL)
    
}
       
 objset_is_shatterable <- function(subset,context){
   reduced_context <- context[which(subset==1),]
   reduced_context <- context[,which(colSums(reduced_context)==sum(subset)-1]
                                     
 return(nrow(unique(t(reduced_context)))==sum(subset)}
                                  
