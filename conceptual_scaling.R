################################################################################
# Conceptual Scaling 
# Note: the nominal scaling is not not completely correct. We have mixed the nominal
# scaling with grouped classes and without. The formal context is computed by the
# nominal scaling without grouped classes and the union-free generic family of 
# implication with grouped classes.
################################################################################
################################################################################
# Formal Context
################################################################################

calculate_nominal_scaling_vec <- function(data_values, add_column_name=NULL) {  
  # nominal scaling the vector
  
  # Input: data values(vector): for each observation one factor value
  #         add_column_name (NULL, char): a further definition for the column names
  
  # Output: dataframe representing the crosstable
  
  attr <- sort(unique(data_values))
  length_attr <- length(attr)
  number_elements_data <- length(data_values)
  
  # Memory sapce
  context_logical <- array(0, c(number_elements_data, length_attr))
  column_names_context <- rep("", length_attr)
  
  # Looping throw all attributes
  for (k in 1:length_attr) {
    # Defining the column name
    column_names_context[k] <- paste(c(add_column_name, ": ", as.character(attr[k])), collapse = "")
    # Defining the entries of the column. TRUE if value has attribute k
    context_logical[ ,k] <- as.integer(data_values == attr[k])
    
  }
  colnames(context_logical) <- column_names_context
  return(context_logical)
}

calculate_ordinal_scaling_vec <- function(data_values, add_column_name = NULL) { 
  # ordinal scaling the vector
  
  # Input: data values (vector): for each observation the corresponding numeric value
  #         add_column_name (NULL, char): a further definition for the column names
  
  # Output: dataframe representing the crosstable
  
  data_values <- as.numeric(as.character(data_values))
  
  attr <- sort(unique(data_values))
  length_attr <- length(attr)
  number_elements_data <- length(data_values)
  
  # Memory space
  context_logical <- array(0, c(number_elements_data,length_attr))
  colnames_context <- rep("",length_attr)
  
  # Loop throw all attributes
  t = 1
  for (k in (1:length_attr)) {
    # Defining the column name
    colnames_context[k] <- paste(c(add_column_name,": x<=", attr[k]), collapse = "")
    # Defining the entries of the column. TRUE if value is smalles than attr
    context_logical[ ,k] <- (data_values <= attr[k])
  }
  
  # Changing the colnames of the produced context
  colnames(context_logical) <- colnames_context
  
  return(context_logical)
}


calculate_dual_ordinal_scaling_vec <- function(data_values, add_column_name = NULL) { 
  # dual-ordinal (meaning >= instead of <=) scaling the vector
  
  # Input: data values (vector): for each observation the corresponding numeric value
  #         add_column_name (NULL, char): a further definition for the column names
  
  # Output: dataframe representing the crosstable
  
  data_values <- as.numeric(as.character(data_values))
  
  attr <- sort(unique(data_values))
  lenght_attr <- length(attr)
  number_elements_data <- length(data_values)
  
  # Memory space
  context_logical <- array(0,c(number_elements_data,lenght_attr))
  colnames_context <- rep("",lenght_attr)
  
  # Loop throw all attributes
  t = 1
  for (k in (1:lenght_attr)) {
    # Defining the column name
    colnames_context[k] <- paste(c(add_column_name, ": x>=", attr[k]), collapse = "")
    # Defining the entries of the column. TRUE if value is larger or equal attr
    context_logical[ ,k] <- (data_values >= attr[k])
  }
  
  # Changing the colnames of the produced context
  colnames(context_logical) <- colnames_context
  
  return(context_logical)
}



# Auxiliary function for calculate_conceptual_scaling
calculate_number_columns_attr <- function(data_matrix){ 
  # This function is needed to calculate the number of attributes needed to 
  # represent each column. This depends on the used class of the values in the
  # column.
  
  # Input: data_matrix (dataframe): each row represents one attribute 
  #                                 (not necessarily two-valued)
  
  # Output (list): number of attributes needed (all and per attribute), 
  #                 the column names and the class of the elements
  
  number_attr <- dim(data_matrix)[2]
  colnames_data <- colnames(data_matrix)
  
  # Memory space
  number_column_per_attr <- rep(0, number_attr)
  column_names <- NULL
  class_elements_columns <- rep("", number_attr)
  
  # Looping throw all attrbutes given by the input
  for (k in (1:number_attr)) {
    # Saving which mode have the elements in column k 
    class_elements_columns[k] <- class(data_matrix[ ,k])
    
    # if the mode is "ordered", "numeric" or "integer" the values are ordinal and
    # dual-ordinal saved and hence we have 2*(number of different values in column k)
    if (class(data_matrix[,k])[1] == "ordered" |
        class(data_matrix[,k])[1] == "numeric" |
        class(data_matrix[,k])[1] == "integer") {
      number_column_per_attr[k] <- 2 * length(unique(data_matrix[ ,k]))
    }
    # if the mode of column k is "factor" for each value one column is needed
    if (class(data_matrix[,k])[1] == "factor" ) {
      number_column_per_attr[k] <- length(unique(data_matrix[,k]))
    }
    
    # Now we save the colnames by adding to the already defined ones 
    column_names <- c(column_names, rep(colnames_data[k], number_column_per_attr[k]))
  }
  
  return(list(class_elements_columns = class_elements_columns,
              number_column_per_attr = number_column_per_attr,
              number_column_all_attr = sum(number_column_per_attr),
              column_names = column_names))
}


calculate_conceptual_scaling <- function(data_matrix) {  
  # main function for scaling automatically
  
  # Input: data_matrix (dataframe): each row represents one attribute 
  #                                 (not necessarily two-valued)
  
  # Output (matrix): Scaled crosstable
  
  number_obj <- dim(data_matrix)[1]
  number_attr <- dim(data_matrix)[2]
  colnames_data <- colnames(data_matrix)
  
  number_columns_needed <- calculate_number_columns_attr(data_matrix)
  
  # Memory spaces
  context_converted <- array(0,c(number_obj, number_columns_needed$number_column_all_attr))
  colname_context <- rep("", number_columns_needed$number_column_all_attr)
  
  t = 1
  for (k in (1:number_attr)) {
    # print(c(k,": ",class(data_attr_obj[,k])),quote=FALSE)
    
    if (class(data_matrix[ ,k])[1] == "ordered" | 
        class(data_matrix[ ,k])[1] == "numeric" | 
        class(data_matrix[ ,k])[1] == "integer") { 
      # Calculating the context for the attribute k
      inner_context  <-  cbind(calculate_ordinal_scaling_vec(as.numeric(data_matrix[ ,k]),
                                                             colnames_data[k]),
                               calculate_dual_ordinal_scaling_vec(as.numeric(data_matrix[ ,k]),
                                                                  colnames_data[k]))
      # number of columns needed for saving
      column_number_k <- number_columns_needed$number_column_per_attr[k] - 1
      
      # Saving
      context_converted[ , t:(t + column_number_k)] <- inner_context
      colname_context[t:(t + column_number_k)] <- colnames(inner_context)
      
      t <- t + column_number_k + 1
    }
    if (class(data_matrix[,k])[1] == "factor") {
      # Calculating the context for the attribute k
      inner_context <- calculate_nominal_scaling_vec(data_matrix[,k],
                                                     colnames_data[k]) 
      # number of columns needed for saving
      column_number_k <- number_columns_needed$number_column_per_attr[k] - 1
      
      # Saving
      context_converted[ , t:(t + column_number_k)] <- inner_context
      colname_context[t:(t + column_number_k)] <- colnames(inner_context)
      
      t <- t + column_number_k + 1
    }
  } 
  
  # Changing colnames
  colnames(context_converted) <- colname_context
  
  return(context_converted)
}


################################################################################
# calculate conclusion
################################################################################
calculate_interordinal_conclusion <- function(premise, list_info) {
  
  # This function calculates the conclusion based on interordinal scaled attribute
  
  # @premise (vector of (0,1)): 1 represents that the point is within the 
  #                             subset
  # @list_info (containing data_values): numeric attribute of each observation 
  #                                      (same length as premise)
  
  # Output (list): the premise input and the conclusion, two vectors with elements
  #                in 0 and 1, with 1 representing that the observation is in the
  #                set
  
  
  data_values <- list_info$data_values
  index_premise <- which(premise == 1)
  
  inner_conclusion <- rep(0, length(data_values))
  
  # every point with attribute being between maximal and minimal attribute value
  # of the subset is within the premises
  if (sum(index_premise) > 0) {
    min_premise_value <- min(data_values[index_premise])
    max_premise_value <- max(data_values[index_premise])
    
    index_conclusion <- which((data_values >= min_premise_value) & (data_values <= max_premise_value))
    
    inner_conclusion[index_conclusion] <- 1
    inner_conclusion[index_premise] <- 1
  }
  
  
  return(list(premise = premise, conclusion = inner_conclusion))
}


calculate_nominal_conclusion <- function(premise, list_info){
  
  # This function calculates the conclusion based on nominal scaled attribute
  
  # @premise (vector of (0,1)): 1 represents that the point is within the 
  #                             subset
  # @list_info (containing data_values): nominal attribute of each observation 
  #                                      (same length as premise)
  
  # Output (list): the premise input and the conclusion, two vectors with elements
  #                in 0 and 1, with 1 representing that the observation is in the
  #                set
  
  data_values <- list_info$data_values
  index_premise <- which(premise == 1)
  inner_conclusion <- rep(0, length(data_values))
  
  # if only one attribute value is in the premises, then the conclusion contains
  # each observation with the same attribute value
  # If two or more attributes occur in the premise, then no attribute holds for
  # every element in the premise and thus, the entire set is the conclusion
  if (sum(index_premise) > 0)  {
    premise_value <-  unique(data_values[index_premise])
    if (length(premise_value) > 1) {
      inner_conclusion <- rep(1, length(data_values))
    }
    if (length(premise_value) == 1) {
      index_conclusion <- which(data_values %in% premise_value)
      inner_conclusion[index_conclusion] <- 1
    }
  }
  return(list(premise = premise, conclusion = inner_conclusion))
}

################################################################################
# - union-free generic family of implications
################################################################################
calculate_gufimpl_interordinal_sumgurobi <- function(data_values,
                                                    calculate_conclusion = calculate_interordinal_conclusion) {
  
  # This function calculates the union--free generic family of implication for
  # interordinal scaled attributes
  
  # @data_values (vector): numeric attribute of each observation 
  # @calculate_conclusion (function): calculates the conclusion of interordinal
  #                                   scaled attributes
  
  # Output (list): A - describes the family of implications
  #                length_premise - the length of the premise corresponding to the 
  #                                 rows of A
  #               REST - for gurobi calculation
  
  number_obj <- length(data_values)
  attr_sorted <- sort(unique(data_values))
  length_attr <- length(attr_sorted)
  
  
  # Memory space for saving the parts to calculate a triple matrix
  i_row <- list()
  j_column <- list()
  v_value <- list()
  length_premise <- list()
  
  count_implication <- 1
  
  # Each premise consists of two points, because we are not interested in trivial 
  # implications the premise values are at least two values apart.
  
  for (count_attr_upper in seq(3, length_attr)) {
    for (count_attr_lower in seq(1,count_attr_upper - 2)) {
      index_attr_upper <- which(data_values == attr_sorted[count_attr_upper])
      index_attr_lower <- which(data_values == attr_sorted[count_attr_lower])
      
      inner_premise <- rep(0, number_obj)
      index_inner_premise <- c(index_attr_lower, index_attr_upper)
      inner_premise[index_inner_premise ] <- 1
      
      inner_conclusion <- calculate_conclusion(inner_premise, list(data_values = data_values))$conclusion
      inner_conclusion[index_inner_premise] <- 0
      index_inner_conclusion <- which(inner_conclusion  == 1)
      
      size_conclusion <- length(index_inner_conclusion)
      size_premise <- length(index_inner_premise)
      
      # Saving the conclusion
      i_row <- append(i_row, rep(count_implication, size_conclusion))
      j_column <- append(j_column, index_inner_conclusion)
      v_value <- append(v_value, rep(-1/size_conclusion, size_conclusion))
      
      
      # Saving premise
      i_row <- append(i_row, rep(count_implication, size_premise))
      j_column <- append(j_column, index_inner_premise)
      v_value <- append(v_value, rep(1, size_premise))
      
      length_premise <- append(length_premise, length(index_inner_premise))
      
      count_implication <- count_implication + 1
      
    }
  }
  
  # Now we have to include the duplicated ones
  
  for (count_attr in attr_sorted) {
    index_attr <- which(data_values == attr_sorted[count_attr])
    
    # Test if this value exists twice
    if (length(index_attr) > 1) {
      for (count_index_premise in 1:length(index_attr)) {
        size_premise <- 1
        index_inner_premise <- index_attr[count_index_premise]
        
        size_conclusion <- length(index_conclusion) - 1
        index_inner_conclusion <- index_attr[count_index_premise]
        
        # Saving the conclusion
        i_row <- append(i_row, rep(count_implication, size_conclusion))
        j_column <- append(j_column, index_inner_conclusion)
        v_value <- append(v_value, rep(-1/size_conclusion, size_conclusion))
        
        
        # Saving premise
        i_row <- append(i_row, rep(count_implication, size_premise))
        j_column <- append(j_column, index_inner_premise)
        v_value <- append(v_value, rep(1, size_premise))
        
        length_premise <- append(length_premise, length(index_inner_premise))
        
        count_implication <- count_implication + 1
        
      }
    }
  }
  
  # Test if all implications are redundant and if yes, replace constrains by a trivial one.
  # And return this object.
  if (length(i_row) == 0) {
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
  
  i_row <- as.array(unlist(i_row))
  j_column <- as.array(unlist(j_column))
  v_value <- as.array(unlist(v_value))
  length_premise <- as.array(unlist(length_premise))
  
  count_implication <- count_implication - 1
  # Starting the garbage collection
  gc()
  
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



calculate_gufimpl_nominal_sumgurobi <- function(data_values,
                                                calculate_conclusion = calculate_nominal_conclusion) {
  
  # This function calculates the union--free generic family of implication for
  # nominal scaled attributes
  
  # @data_values (vector): factor attribute of each observation 
  # @calculate_conclusion (function): calculates the conclusion of nominal
  #                                   scaled attributes
  
  # Output (list): A - describes the family of implications
  #                length_premise - the length of the premise corresponding to the 
  #                                 rows of A
  #               REST - for gurobi calculation
  
  number_obj <- length(data_values)
  attr_unique <- unique(data_values)
  length_data_values <- length(data_values)
  
  # Memory space for saving the parts to calculate a triple matrix
  i_row <- list()
  j_column <- list()
  v_value <- list()
  length_premise <- list()
  
  count_implication <- 1
  
  
  if (length(attr_unique) == 1) {
    warning("this nominal covariable has no impact since only one class exists. It can be ignored.")
    
    for (index_premise in 1:number_obj) {
      
      index_inner_conclusion <- (1:number_obj)[-index_premise]
      
      # Saving the conclusion
      i_row <- append(i_row, rep(count_implication, number_obj - 1))
      j_column <- append(j_column, index_inner_conclusion)
      v_value <- append(v_value, rep(-1/(number_obj - 1), number_obj - 1))
      
      
      # Saving premise
      i_row <- append(i_row, rep(count_implication,1))
      j_column <- append(j_column, index_premise)
      v_value <- append(v_value, rep(1, 1))
      
      length_premise <- append(length_premise, length(index_premise))
      
      count_implication <- count_implication + 1
    }
    
    i_row <- as.array(unlist(i_row))
    j_column <- as.array(unlist(j_column))
    v_value <- as.array(unlist(v_value))
    length_premise <- as.array(unlist(length_premise))
    
    count_implication <- count_implication - 1
    
    # Starting the garbage collection
    gc()
    
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
  
  
  # Each premise consists of one observation
  
  for (index_premise in seq(1, length_data_values)) {
    
    inner_premise <- rep(0, number_obj)
    inner_premise[index_premise] <- 1
    
    inner_conclusion <- calculate_conclusion(inner_premise, list(data_values = data_values))$conclusion
    inner_conclusion[index_premise] <- 0
    index_inner_conclusion <- which(inner_conclusion  == 1)
    
    size_conclusion <- length(index_inner_conclusion)
    size_premise <- 1
    
    if (size_conclusion != 0) {
      # Saving the conclusion
      i_row <- append(i_row, rep(count_implication, size_conclusion))
      j_column <- append(j_column, index_inner_conclusion)
      v_value <- append(v_value, rep(-1/size_conclusion, size_conclusion))
      
      
      # Saving premise
      i_row <- append(i_row, rep(count_implication, size_premise))
      j_column <- append(j_column, index_premise)
      v_value <- append(v_value, rep(1, size_premise))
      
      length_premise <- append(length_premise, length(index_premise))
      
      count_implication <- count_implication + 1
    }
  }
  
  # Test if all implications are redundant and if yes, replace constrains by a trivial one.
  # And return this object.
  if (length(i_row) == 0) {
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
  
  i_row <- as.array(unlist(i_row))
  j_column <- as.array(unlist(j_column))
  v_value <- as.array(unlist(v_value))
  length_premise <- as.array(unlist(length_premise))
  
  count_implication <- count_implication - 1
  # Starting the garbage collection
  gc()
  
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




################################################################################
# calculate the generator of the closure of a subset which lies within the 
# subset
################################################################################
calculate_generator_interordinal <- function(subset, list_info) {
  
  # This function calculates the generator of a subset based on interordinal 
  # scaled attribute
  
  # @subset (vector of (0,1)): 1 represents that the point is within the 
  #                             subset
  # @list_info (containing data_values): numeric attribute of each observation 
  #                                      (same length as premise)
  
  # Output (list): the generator of the closure of subset, vectors with elements
  #                in 0 and 1, with 1 representing that the observation is in the
  #                set
  
  
  data_values <- list_info$data_values
  index_subset <- which(subset == 1)
  
  # the closure of the empty set is the empty set and for one point it is this
  # point, since we assume no duplication exists.
  if (length(index_subset) <= 1) {
    return(list(subset))
  }
  
  # The generator is smallest and the largest attribute value
  min_subset_value <- min(data_values[index_subset])
  max_subset_value <- max(data_values[index_subset])
  
  index_min <- which(data_values == min_subset_value)
  index_max <- which(data_values == max_subset_value)
  
  # Obtain all values which are within the subset and also have min/max value
  index_min_subset <- intersect(index_subset, index_min)
  index_max_subset <- intersect(index_subset, index_max)
  
  generator <- list()
  for (count_lower in index_min_subset) {
    for (count_upper in index_max_subset) {
      inner_generator <- rep(0, length(data_values))
      inner_generator[c(count_lower, count_upper)] <- 1
      
      generator <- append(generator, list(inner_generator))
    }
  }
  return(generator)
}


calculate_generator_nominal <- function(subset, list_info) {
  
  # This function calculates the generator of a subset based on nominal 
  # scaled attribute
  
  # @subset (vector of (0,1)): 1 represents that the point is within the 
  #                             subset
  # @list_info (containing data_values): factor attribute of each observation 
  #                                      (same length as premise)
  
  # Output (list): the generator of the closure of subset, vectors with elements
  #                in 0 and 1, with 1 representing that the observation is in the
  #                set
  
  
  data_values <- list_info$data_values
  subset <- calculate_nominal_conclusion(subset, list_info = list_info)$conclusion
  index_subset <- which(subset == 1)
  
  # the generator of the empty set is the empty set
  if (length(index_subset) < 1) {
    return(list(subset))
  } 
  
  subset_values <- data_values[index_subset]
  generator <- list()
  
  # If every element of the closure has the same attribute value, each element
  # of which has this attribute is a generator 
  if (length(unique(subset_values)) == 1) {
    for (counter in index_subset) {
      inner_generator <- rep(0, length(data_values))
      inner_generator[counter] <- 1
      generator <- append(generator, list(inner_generator))
    }
  } else {
    # Each subset which contains two different factor values is a generator
    for (count_1 in 1:(sum(subset) - 1)) {
      for (count_2 in (count_1 + 1):sum(subset)) {
        index_1 <- index_subset[count_1]
        index_2 <- index_subset[count_2]
        if (data_values[count_1] != data_values[count_2]) {
          inner_generator <- rep(0, length(data_values))
          inner_generator[c(index_1, index_2)] <- 1
          generator <- append(generator, list(inner_generator))
        }
      }
    }
  }
  
  return(generator)
}


