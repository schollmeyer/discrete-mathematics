################################################################################
# fca_ufg_partial_order
################################################################################

################################################################################
# Very general help function
################################################################################

supress_warning_vector_and_isna <- function(text) {
  if (any( grepl("the condition has length > 1 and only the first element will be used", text))) {
    invokeRestart("muffleWarning")
  }
}

################################################################################
# one single partial order
################################################################################

### compute the transitive hull
compute_relation_product <- function(X,Y){ 
  
  # @X (matrix): Represents a graph with edges (weight one) and knots
  # @Y (matrix): Represents a graph with edges (weight one)and knots
  # Return (matrix): Represents a graph after two steps which are defined by X and Y
  
  # Input check
  if (dim(Y)[1] != dim(X)[1]) {
    print("dimension missmatch!")
    stop
  }
  
  number_row_X <- dim(X)[1]
  number_col_X <- dim(X)[2]
  number_col_Y <- dim(Y)[2]
  
  product_result <- array(0, c(number_row_X, number_col_Y))
  
  for (k in (1:number_col_X)) {
    # X[.,k] edge between . to k 
    # Y[k,.] edge from k to .
    
    # computes if there is a path which uses knot k as intermediate step
    product_result[which(X[,k] == 1), which(Y[k,] == 1)] <- 1
  }
  
  return(product_result)
}

compute_transitive_hull <- function(relation_mat) {
  
  # @relation_mat (sqared matrix): represents a relation matrix
  # Return (squared matrix): the transitive hull of the relation matrix relation_mat
  
  number_obj <- dim(relation_mat)[1]
  
  old_matrix <- array(0,c(number_obj, number_obj))
  next_matrix <- relation_mat
  transitive_hull <- relation_mat
  
  # each while-loop computes the next step of the path given by relation_mat
  while (any(old_matrix != next_matrix)) {
    old_matrix <- next_matrix
    # this computes the next step. In other words in the first loop it computes
    # all edges which can be obtained by the combination of twp edges in relation_mat
    next_matrix <- compute_relation_product(old_matrix, relation_mat)
    
    # contains all paths which can be done in maximal number of loop iteration of steps
    transitive_hull <- transitive_hull + next_matrix
  }
  
  # more than one possible path --> than the number of paths was computed by the while-loop
  # --> set to 1
  index_non_zero <- which(transitive_hull > 0)
  transitive_hull[index_non_zero] <- 1
  
  return(transitive_hull)
}


### uniformly sample a partial order (based on IPMU Paper)
sample_uniformly_partial_order <- function(item_number){
  # we set f(g) constant to 1/ (2^n) then the condition stated given after the 
  # Algortihm is true
  # TODO
  # Besser kleinste obere Schranke die du kennst anwenden
  
 
  
  # sampling uniformly a total order. Use Fisher-Yates-Process
  # https://de.wikipedia.org/wiki/Zuf%C3%A4llige_Permutation#Erzeugung
  
  lin_order <- seq(1, item_number)
  for (i in rev(seq(2, item_number))) {
    z <- sample(1, seq(1, i))
    lin_order[c(i,z)] <- lin_order[c(z,i)]
  }
  
  # representing the linear order by is transitive hull
  lin_order_mat <- matrix(rep(0, item_number*item_number), nrow = item_number)
  diag(lin_order_mat) <- rep(1, item_number)
  for (i in seq(1, item_number - 1)) {
    lin_order_mat[lin_order[i], lin_order[i + 1]] <- 1
  }
  
  # uniformly deleting del_pair many pairs (uniformly sample a subset of cardinality del_pairs)
  # a linear order has n(n-1) many pair and we are number consecutilvely by row
  # of the matrix
  del_pairs <- sample(1, seq(1, (items - 1)*items / 2))
  index_pairs <- sample(seq(1, n*(n-1)), size = del_pairs, replace = FALSE)
  
  part_order_mat[TODO] <- rep(0, del_pairs)
  transitive_hull <- TODO
  transitive_reduction <- TODO 
    
  # Computing the acceptance probability
  
  number_lin_extensions <- TODO
  accept_prob <- f * (1 / 2^(4)) # nochmal kontrollieren ob da wirklch dieses ganze 2^-n jdpb wegfällt
  
  
  return(transitive_hull)
}


### check if partial order

test_if_porder <- function(po_candidate) {
  # @po_candidate(quardatic matrix with 0,1 value)
  
  # return (logical)
  
  # Step 1: check if cycle exists
  diag(po_candidate) <- rep(0, dim(po_candidate)[1])
  if (is.na(Rfast::topological_sort(po_candidate))) {
    return(FALSE)
  }
  
  # # Step 2 Check if the transitivity holds (i.e. a<b and b<c but also a and c are not comparable is not allowed)
  # Here, we use that each pair is 
  # thus if the transitive hull is unequal to the relation itself, then it is not a transitive
  # We use the function in fca_ufg_partial_order.r
  diag(po_candidate) <- rep(1, dim(po_candidate)[1])
  return(all(compute_transitive_hull(po_candidate) == po_candidate)) # this tolerance is sufficient since only 0 or 1 exists
}


################################################################################
# formal context of partial orders
################################################################################

### formal context based on a subset of partial order (definition)
compute_fc_subset_porders <- function(partial_orders) {
  # @partial_orders(list of matrices): each matrix represents a partial order 
  # IMPORTANT: As computation is much easier to understand if reflexiv part is added,
  # we leave this redundant row!!!!!!!!
  
  if (!is.list(partial_orders)) {
    return(c(c(partial_orders), !c(partial_orders)))
  }
  
  fc <- matrix(, ncol = length(partial_orders[[1]]) * 2, nrow = length(partial_orders))
  
  for (i in 1:length(partial_orders)) {
    fc[i, ] <- c(partial_orders[[i]], !partial_orders[[i]])
  }
  
  return(fc)
}



### closure of the fca based on the set of all partial orders fca
# wird vermutlich für test gebraucht

compute_closure_fc_porders_obj <- function(premise) {
  #@premise: a list of partial orders, each partial order is given by its adjacency matrix
  # TODO
  if (length(premise) <= 1) {
    return(premise)
  }
  
  item_number <- dim(premise[1])[1]
  
  conclusion <- premise
  intersection <- prod(premise)
  union <- any(!premise)
  
  difference <- union - intersection
  index_difference <- which(difference == 1)
  
  possible_subsets <- unlist(lapply(1:length(index_difference),combinat::combn, 
                                    x = index_difference,
                                    simplify = FALSE), 
                              recursive = FALSE)
  
  for (i in 1:length(possible_subsets)) {
    candidate_po <- union
    candidate_po[possible_subsets[i]] <- 1
    
    if (test_if_porder(candidate_po)) {
      append(conclusion) <- candidate_po
    }
  }
  
  # delete duplicates
  # TODO
  
  return(conclusion)
  
}


# compute_phi_attr <- function(attr_set) {
  # @list of attributes
  
  # TODO
# }

compute_intent <- function(partial_orders) {
  # TODO does it also work for length(partial_orders) == 1?? REst sollte gehen
  fc_ufg <- compute_fc_subset_porders(partial_orders)
  
  if (!is.list(partial_orders)) { # only one order as input
    return(which(fc_ufg == 1))
  }
  
  return(which(colSums(fc_ufg) == dim(fc_ufg)[1]))
}

compute_disting_attr <- function(partial_orders) {
  
  # this is done vio the formal subcontext
  fc <- compute_fc_subset_porders(partial_orders)
  
  distingishable_set <- as.list(rep(NA, length(partial_orders)))
  index_disting_general <- which(colSums(fc) == dim(fc)[1] - 1)
  
  for (index_po in seq(1, length(partial_orders))) {
    distingishable_set[[index_po]] <- index_disting_general[which(fc[index_po, index_disting_general] == 0)]
  }
  
  return(distingishable_set)
}



################################################################################
# ufg considerations based on 
################################################################################
### test if ufg 

test_if_ufg_partial <- function(ufg_candidate) {
  
  # the number of elements must be strictly larger than 1 (else trivial)
  if (length(ufg_candidate) <= 1 || is.matrix(ufg_candidate)) {
    return(FALSE)
  }
  
  # check if generator
  cardinality_ufg <- length(ufg_candidate)
  fc_sub <- compute_fc_subset_porders(ufg_candidate)
  attr_distinguish <- which(colSums(fc_sub) == (cardinality_ufg - 1))
  
  # If cardinality of attr_distinguish is 1, what follows produces an error thus,
  # we have to catch it bevor. As cardianlity_ufg>1 this cannot be an generator
  if (length(attr_distinguish) == 1) {
    return(FALSE)
  }
  
  fc_sub_attr_dist <- fc_sub[, attr_distinguish]
  has_obj_distinguish_attr <- which(rowSums(fc_sub_attr_dist) < length(attr_distinguish))
  
  if (!(length(has_obj_distinguish_attr) == cardinality_ufg)) {
    return(FALSE)
  }
  
  # check if ufg
  # Use that an object which does not ly in any proper subset of ufg_candidate
  # must fulfill that the corresponding intent holds and for each partial order 
  # in ufg_candidate at least one distinguishable element must hold.
  
  intent <- compute_intent(ufg_candidate)
  disting_set <- compute_disting_attr(ufg_candidate)
  
  # Now use that we are only checking if a partial order exists in particular we 
  # check if the "smallest" holding all these conditions exists. 
  # Thus we use that a partial order must either have an pair or not, but both 
  # together is not possible
  number_item <- dim(ufg_candidate[[1]])[1] 
  test_candidate <- matrix(rep(0, number_item  * number_item) , ncol = number_item)
  diag(test_candidate) <- rep(1, number_item) # ??wird nicht benötigt da im intent auch die redundanten reflexiven drin sind
  
  for (index_intent in intent) {
    if (index_intent <= number_item * number_item) {
      test_candidate[index_intent] <- 1
    }
  }
  
  possible_constraints_by_disting <- expand.grid(disting_set)
  # add the intersection as possible constraint
  possible_constraints_by_disting[dim(possible_constraints_by_disting)[1] + 1, ] <- 
    rep(2 * number_item * number_item + 1, dim(possible_constraints_by_disting)[2])
  
  
  for (index_disting in seq(1, dim(possible_constraints_by_disting)[1])) {
    test_candidate_inner <- test_candidate
    
    for (index_intent in possible_constraints_by_disting[index_disting, ]) {
      if (index_intent <= number_item * number_item) {
        test_candidate_inner[index_intent] <- 1
      }
    }
    
    test_candidate_inner <- compute_transitive_hull(test_candidate_inner)
    
    # check if text_candidate_inner is one of the ufg_candidate
    next_loop <- FALSE
    for (candidate in ufg_candidate) {
      if (all(candidate == test_candidate_inner)) {
        next_loop <- TRUE # need for going on with next outer for loop -- see below
        break # ending for-loop
      }
    }
    if (next_loop) {
      next  # going to next for-loop iteration
    }
    
    # check if this test_candidate_inner fulfills also the nonedges attributes
    intent_test_candidate_inner <- compute_intent(test_candidate_inner)
    if (!(setequal(intersect(intent_test_candidate_inner, intent), intent))) {
      next # going to next for-loop iteration
    }
    if (test_if_porder(test_candidate_inner)) {
      return(TRUE)
    }
  }
  
  # we didn't found a possible b which is only contained in the entire set but in
  # non subset --> Thsus, return false
  return(FALSE)
}


### samplin an ufg premise given a data set of partial orders

sample_from_data_ufg_partial <- function(data_po, break_by = 60, sample_size = 30) {
  
  
  result <- list()
  for (sample_index in seq(1, sample_size)) {
    while_break_index <- 1
    stay_in_while <- TRUE
    
    item_number <- dim(data_po[[1]])[1]
    while (stay_in_while) {
      random_size <- sample(seq(2, item_number * item_number * 1/2), 1)
      ufg_index <- sample(seq(1, length(data_po)), random_size)
      ufg <- data_po[ufg_index]
      # ACHTUNG: Glaube dass das noch falsch ist, da dabei kleine ufg's bevorzugt werden
      
      # print(ufg) # das mache ich nur gerade, da irgendwo ein problem mit test besteht...
      # ufg_outside <<- ufg #!!ACHTUNG UNBEDINGT LÖSCHEN SOBALD FEHLER GEFUNDEN!!!!
      if (test_if_ufg_partial(ufg)) {
        result <- append(result, ufg)
        stay_in_while <- FALSE
      }
      
      
      while_break_index <- while_break_index + 1
      if (while_break_index > break_by) {
        result <- append(result, "stopped while loop")
        stay_in_while <- FALSE
      }
    }
  }
  return(result)
  
}


### sampling an ufg premise

sample_uniformly_ufg_partial <- function(item_number, break_by = 60) {
  # TODO noch nicht kontrolliert
  while_break_index <- 1
  
  while (TRUE) {
    random_size <- sample(seq(2, item_number * item_number * 1/2), 1)
    ufg <- lapply(rep(item_number, random_size), FUN = sample_uniformly_partial_order)
    # ACHTUNG: Glaube dass das noch falsch ist, da dabei kleine ufg's bevorzugt werden
    
    
    if (test_if_ufg_partial(ufg)) {
      return(ufg)
    }
    
    
    while_break_index <- while_break_index + 1
    if (while_break_index > break_by) {
      return("stopped while loop")
    }
  }
}



new_sample_uniformly_ufg_partial <- function(item_number) {
  # TODO
  # zufällig ziehen einer Teilmenge und dann testen ob diese eine ufg ist
  
  # hierbei könnte man einbauen, dass kleine Teilmengen von partiellen Ordnungen wahrscheinlicher gewählt werden
  # --> qird auch hier gemacht
  
  random_size <- sample(seq(2, item_number * item_number * 1/2), 1)
  
  
  # if (all.equal(random_size, 1)) {
  #   
  # }
  
  if (all.equal(random_size, 2)) {
    
  }
  
  distingishable_set <- list(rep(NA, random_size))
  corresp_intent <- list()
  ufg <- list()
  
  
  ufg <- append(ufg, sample_uniformly_partial_order(item_number))
  ufg <- append(ufg, sample_uniformly_partial_order(item_number))
  
  test_if_ufg_partial(ufg)
  
  # the next ufg elements are added systematically
  for (ufg_current_size in seq(3, random_size)) {
    fc_ufg_i <- compute_fc_subset_porders(ufg)
    corresp_intent <- which(rowSums(fc_ufg_i) == dim(fc_ufg_i)[1])
    
    index_disting_general <- which(rowSums(fc_ufg_i) == dim(fc_ufg_i)[1] - 1)
    
    for (index_ufg in seq(1, length(ufg))) {
      distingishable_set[[index_ufg]] <- index_disting_general[which(fc_ufg_i[index_ufg, index_disting_general] == 0)]
    }
    
    # Now, we sample a partial order which has at least one new distinguisable 
    # element w.r.t current ufg and for each current distinguishable elements w.r.t
    # one ufg element stays.
    
    # Step 1: Sample a proper,  subset of correps_inten (will be the new one)
    # is done by choosing a randomn natural binary number between 1 and 2^#corresp_intent
    
    index_new_corresp_intent <- as.logical(inToBits(sample(seq(0, 2^{length(corresp_intent)} - 1), 1)))
    deleted_intent <- corresp_intent[!index_new_corresp_intent]
    corresp_intent <- corresp_intent[index_new_corresp_intent] 
    # note that the indices larger than length(new_corresp_intent) are FALSE
    
    # STAR Note that all attributes not in the new correps_intent set are not allowed to hold
    # Since we are sampling an partial order the oposite must be true, this means
    # if has_pair lies only in the old intent, then now has_not_pair must be true for
    # the new sampled partial order (the same holds for the reverse)
    
    
    # Step 2: Sample for each old ufg element at least one attribute which stays
    # distinguishable
    
    new_disting_set <- list(rep(NA, random_size))
    new_disting_set[ufg_current_size] <- delet_intent
    new_compl_disting_set <- list(rep(NA, random_size))
    for (index_ufg in seq(1, length(ufg))) {
      index_new_disting <- as.logical(inToBits(sample(seq(1, 2^(length(index_disting_general[index_ufg]))), 1)))
      new_disting_set[index_ufg] <- index_disting_general[index_ufg][index_new_disting]
      new_compl_disting_set[index_ufg] <- index_disting_general[index_ufg][!index_new_disting]
      # Note that the an analogous argument as in STAR can be applied here
    }
    
    # Step 3: sort conditions on the new partial order (pairs it must has, and it is not allowed to have)
    
    # Explanation
    # pair must exist if 1. lies in corrsp_intent and index_number is smaller than item*(item-1)
    #                   2. lies in index_new_disting and ----------------------"----------------------
    #                   3. lies in deleted_intent and index_number larger/equal than item * (item -1) +1
    #                   4. lies in new_compl_disting_set -------------------------"---------------------
    # pair does not exist if 1. lies in corrsp_intent and index_number larger/equal than item * (item -1) +1
    #                   2. lies in index_new_disting and ----------------------"----------------------
    #                   3. lies in deleted_intent and index_number is smaller than item*(item-1)
    #                   4. lies in new_compl_disting_set -------------------------"--------------------- 
    
   
    # Sampling randomly a partial order restricted on these conditions above
    
    # break if not possible to compute such an partial order
    
    # TODO Rest oben steht die Idee 
                                     
  }
  
  
  # Computing the acceptance probability
  # TODO
}







