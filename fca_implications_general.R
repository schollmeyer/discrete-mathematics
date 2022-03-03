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






