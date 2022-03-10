sample_shatterable_K_objset <- function(context,K,subset=rep(0,nrow(context))){
  if(sum(subset)==K){return(subset)}
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
  
  
 


sample_shatterable_K_ufg_candidate <- function(context,big_context=context,K,subset=rep(0,nrow(context)),vector=NULL){
  if(sum(subset)==K){return(list(subset,vector)}
  extent <- operator_closure_obj_input(subset,context)
  idx <- which(extent==0)
  if(sum(subset)==0){
    new_subset <- subset
	new_subset[sample((1:nrow(context)),size=1)]=1
	
	return(sample_shatterable_K_ufg_candidate(context,big_context,K,new_subset,vector=which(new_subset==1)))
  }
	
number_ignored_sets <- number_ignored_sets + length(which(extent==1 & subset==0))
  for(k in sample(idx)){
  #print(k)
    new_subset <- subset
    new_subset[k] <-1
    if(objset_is_ufg_candidate(new_subset,context,big_context)){return(sample_shatterable_K_ufg_candidate(context,big_context,K,new_subset,vector=c(vector,k)))}
       
    }
    
    return(NULL)
    
}

while(TRUE){e=sample_shatterable_K_ufg_candidate(aa,aa,K=6);if(test_if_union_free_generator(e,aa)){E=unique(rbind(E,e));print(dim(E))}}


                                  
