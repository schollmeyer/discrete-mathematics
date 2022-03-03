################################################################################
# Formal Concept Analysis and implications, specified for spatial statistic
################################################################################
################################################################################
# Preparation of spatstat objects
################################################################################
reduce_random_point_pattern <- function(point_pattern, number_points) {
  # reduces the number of points of a ppp-object (spatstat)
  
  # @point_pattern (ppp): planar point pattern given by (spatstat)
  # @number_points (integer): number of points to select
  
  # Output (ppp): reduced planar point pattern
  
  selected_indexes <- sample(1:npoints(point_pattern), number_points)
  retain <- rep(FALSE, npoints(point_pattern))
  retain[selected_indexes] <- TRUE
  return(point_pattern[retain])
}
  
extract_points_from_pattern <- function(point_pattern, which_mark) {
  # This function extracts the points of a ppp-object (spatstat) and the marks
  
  # @point_pattern (ppp): a planar point pattern used within spatstat
  # @which_mark (character): character which is one of the marked used
  #                          in point_pattern
  
  # Output: point matrix defining the observations together with the correpsonding marks
  
  return(list(point_matrix = array(c(point_pattern[["x"]], point_pattern[["y"]]),
                                    c(npoints(point_pattern), 2)),
              mark_values = point_pattern[["marks"]][[which_mark]]))
}

convert_image_to_indices_matrix <- function(attributes_image, point_pattern, 
                                            plotting = FALSE) {
  # Extracts the values at points of an pixel image (spatstat)
  
  # @attribute_image (im): image used in the spatstat environment
  # @point_pattern (ppp): planar point pattern, where the window is within
  #                       attribute_image
  # @plotting (logical): if a plot should be drawn
  
  # Output (vector): the attribute values corresponding to the observations
  #                   given by point_pattern
  
  
  if (plotting) {
    plot(attributes_image)
    points(point_pattern, pch = 1)
    points(point_pattern, pch = 3)
  }
  
  
  return(attributes_image[point_pattern])
}




################################################################################
# Formal Concepts defined by (points, halfspaces, is in halfspace--relation)
# cross tabel / incidence
################################################################################
calculate_context_spatial_attr <- function(point_matrix) {
  
  # Defining the formal concept of the geometrical formal concept analysis with
  # object points in R^2 and attributes closed half-spaces and relation: point
  # is in relation to half-space if and only if point is an element of this 
  # half-space. 
  # Since we want to define a redundant formal-context. It is sufficient to 
  # consider only the half-spaces which bounds goes throw two different points
  # (objects)
  
  # @point_matrix (nx2- matrix): represents the considered points (objects)
  
  # output: (list): context (formal context, columns: half_spaces, row: if point within halfspace)
  #                 indexes (describes the index of two points corresponding to the half-space)
  #                 point_matrix (input matrix)
  
  # REMARK: This function does NOT work when all point given by point_matrix are
  # defined upon one line (are collinear)
  # In particular we assume that all points differ

  
  
  # Input check
  # Test if duplicated exist
  if (any(duplicated.matrix(point_matrix))) {
    stop("At least two points are duplicates.")
  }
  
  # Testing if points in point_matrix are collinear
  slope <- (point_matrix[1,2] - point_matrix[2,2]) / (point_matrix[1,1] - point_matrix[2,1])
  further_slopes_compare <- apply(point_matrix, 1, FUN = function(x) {
    identical(unname((point_matrix[1,2] - x[2]) / (point_matrix[1,1] - x[1])), slope) })
  if (all(further_slopes_compare[-1])) {
    stop("Points are collinear.")
  }
  
  
  number_points <- dim(point_matrix)[1]
  
  # Calculation of the number of half-spaces divided by two
  # We divide, because with this we can reduce the number of needed for-loops
  number_halfsp_divided_2 <- number_points*(number_points - 1)/2  # is always integer
  context_first_part <- array(0, c(number_points, number_halfsp_divided_2))
  context_second_part <- context_first_part
  
  # Memory space for index and the designations filled within the for-loops 
  points_def_boundary <- array(0, c(number_halfsp_divided_2, 2))
  names_first_part <- rep("", number_halfsp_divided_2)
  names_second_part <- rep("", number_halfsp_divided_2)
  
  # Functioning of the three loops:
  # Each half-space is defined by its bound, which goes through two points.
  # Remark that one bound defines two half-spaces. Therefore we have defined two 
  # context memories.
  # The first two loops go through all bounds. The third loop considers each point
  # and calculates (using the scalar product) if it is within one of the two
  # half-space.
  
  # Counting how many half-spaces we already went trough
  i <- 1 
  for (k in 1:(number_points - 1)) {
    for (l in (k + 1):number_points) {
      
      # Saving the names of the half-spaces
      names_first_part[i] <- paste(rownames(point_matrix)[k],
                                   rownames(point_matrix)[l], 
                                   "_>=0", 
                                   sep = "")
      names_second_part[i] <- paste(rownames(point_matrix)[k],
                                    rownames(point_matrix)[l],
                                    "_<=0",
                                    sep = "")
      for (m in 1:number_points) {
        # Calculation of the scalar product
        v1 <- point_matrix[k,] - point_matrix[l,]
        v2 <- point_matrix[m,] - point_matrix[l,]
        s <- v1[1] * v2[2 ] - v1[2] * v2[1]
        # Assignment to the half-spaces
        if (s > 0) {
          context_first_part[m,i] <- 1
        }
        if (s < 0) {
          context_second_part[m,i] <- 1
        }
        if (s == 0) {
          context_second_part[m,i] <- 1
          context_first_part[m,i] <- 1
        }
      }
      
      # Saving for each half-space the two spaces which define the boundary
      # in an index way
      points_def_boundary[i,] <- c(k,l)
      
      # Next half-space memory space
      i = i + 1
    }
  }
  
  # Naming the rows and columns
  colnames(context_first_part) <- names_first_part 
  colnames(context_second_part) <- names_second_part
  rownames(context_first_part) <- rownames(point_matrix)
  rownames(context_second_part) <- rownames(point_matrix)
  

  result <- list(context = (cbind(context_first_part,context_second_part)),
                points_def_spatial_boundary = rbind(points_def_boundary, points_def_boundary),
                point_matrix = point_matrix)
  
  
  return(result)
}



#################################################################################
# calculate spatial conclusion
################################################################################
calculate_convex_conclusion <- function(subset_inner, list_info) { 
  
  # We want to obtain the convex hull of subset_inner and all points which lie
  # within this convex hull
  
  # @premise_innner (array elements in 0,1 only three 1's): Points defining the triangle /premise
  # @basic_formal_context (list): Contains the point matrix
  
  # Output: inner_conclusion (array): Denotes the points within the three points in premise
  #         and the premise: smallest convex hull of subset_inner
  
  if (sum(subset_inner) <= 1) {
    return(list(premise = subset_inner, conclusion = subset_inner))
  }

  point_matrix <- list_info$point_matrix
  index_subset_inner <- which(subset_inner == 1)
  subset_inner_point_mat <- point_matrix[index_subset_inner, ]
  
  index_chull_subset <- chull(subset_inner_point_mat)
  index_inner_premise <- index_subset_inner[index_chull_subset]
  inner_premise <- rep(0, dim(point_matrix)[1])
  inner_premise[index_inner_premise] <- 1
  

  convhull_inner_premise <- try(convhulln(subset_inner_point_mat), silent = TRUE)
  inner_conclusion <- inner_premise
    
  if (any(class(convhull_inner_premise) == "try-error")) {
    convex_hull_points <- subset_inner_point_mat[index_chull_subset, ]
    index_point_not_hull <- seq(1, dim(point_matrix)[1])[-index_inner_premise]
    for (point_index in index_point_not_hull) {
      test_chull <- chull(rbind(convex_hull_points, point_matrix[point_index, ]))
      if (identical(sort(test_chull), seq(1, length(index_chull_subset)))) {
        inner_conclusion[point_index] <- 1
      }
    }
  }
  if (!(any(class(convhull_inner_premise) == "try-error"))) {
    inner_conclusion <- as.integer(inhulln(convhull_inner_premise, point_matrix))
  }
  
  
  return(list(premise = inner_premise, conclusion = inner_conclusion))
}



calculate_convex_conclusion_3point_premise <- function(premise, list_info) { 
  # We want to obtain all points which lie within the triangle given by the 
  # three premise points. Therefore, we converse the cartesian coordinates to 
  # barycentric corrdinates and a point lies within the triange iff all three 
  # barycentric coordinate values are larger or equal 0.
  # See: https://de.wikipedia.org/wiki/Baryzentrische_Koordinaten
  
  # @premise (array elements in 0,1 only three 1's): Points defining the triangle /premise
  # @basic_formal_context (list): Contains the formal context, points as objects
  
  # Output: inner_conclusion (matrix): Denotes the points within the three points in premise
  
  # Attention: 'superassignment' operator, assignment in the enclosing environment
  # needed for cart2bary
  
  basic_formal_context <- list_info$basic_formal_context
  premise <<- premise
  inner_premise <- premise
  
  if (identical(sum(premise), 3)) {
    # Convertion to barycentric coordinates (need: geometry package)
    inner_conclusion <- cart2bary(basic_formal_context$point_matrix[as.logical(premise), ], 
                                  basic_formal_context$point_matrix)
    # Automatically: warning about degenerated simplex
    # if yes --> inner_conclusion is per default set to NULL
  } else {
    inner_conclusion <- NULL
    # warning("Premise has not size 3.")
  }
  
  
  # If cart2bary didn't succeed, the points lie within a line hence the premise 
  # is to large
  if (is.null(inner_conclusion)) {
    
    inner_conclusion <- operator_closure_obj_input(premise, basic_formal_context$context)
    
    if (sum(premise) > 1) {
      # Calculating the smallest premise for inner_conclusion, this must be at least
      # of size two, because we assume that all points are unique
      index_premise <- which(inner_premise == 1)
      possible_premise <- combn(index_premise, 2)
      for (index_loop in 1:dim(possible_premise)[2]) {
        premise_loop <- rep(0, length(inner_premise))
        premise_loop[possible_premise[ ,index_loop]] <- 1
        conclusion_smaller <- operator_closure_obj_input(premise_loop, basic_formal_context$context)
        if (identical(conclusion_smaller, inner_conclusion)) {
          inner_premise <- premise_loop
          break
        }
      }
    }
  } else {
    # Select all points within the triangle and converting logical to 0,1
    inner_conclusion <- (((rowMin(inner_conclusion) >= -.Machine$double.eps) * 1) | premise) * 1
    
  }
  
  
  return(list(premise = inner_premise, conclusion = inner_conclusion))
}


################################################################################
# Implication basis for the FCA (points, halfspaces, is in halfspace--relation)
################################################################################

calculate_convex_base <- function(basic_formal_context) { 
  # Calculates basis function for context with points in R^2 as objects and 
  # half-spaces as inputs. It follows that all extents are convex sets and according
  # to Caratheodory's theorem (convex hull) it is sufficient to consider only
  # premises with three points in R^2
  
  # vgl. Bastide et al. 2000
  
  # @basic_formal_context (list): Contains the formal context, points as objects
  # @calculate_premise (func): Function to u the conclusion based on three points
  
  # Output (matrix): Return of all implication the rows of premise and conclusion 
  #                 correspond
  
  # REMARK: trivial implications are also saved
  
  number_obj <- dim(basic_formal_context$context)[1]
  number_premises <- choose(number_obj,3)
  
  # Memory space
  implication_basis <- list()
  implication_basis$premise <- array(as.logical(0), c(number_premises, number_obj))
  implication_basis$conclusion <- array(as.logical(0), c(number_premises, number_obj))
  
  memory_space <- 1
  
  # The loop goes throw all combinations of three points
  for (k in (1:(number_obj - 2))) {
    for (l in ((k + 1):(number_obj - 1))) {
      for (m in ((l + 1):number_obj)) {
        
        # Defining the premise
        inner_premise <- rep(0,number_obj)
        inner_premise[c(k,l,m)] <- 1
        
        # Calculate the conclusion and eventually the smaller premise
        premise_conclusion <- calculate_convex_conclusion_3point_premise(inner_premise, list(basic_formal_context = basic_formal_context))
        #inner_conclusion[c(k,l,m)] <- 0  wurde hier jetzt nicht auf null gesetzt
        
        # Saving
        implication_basis$premise[memory_space, (1:number_obj)] <- premise_conclusion$premise
        implication_basis$conclusion[memory_space, (1:number_obj)] <- premise_conclusion$conclusion
        
        memory_space <- memory_space + 1
      }
    }
  }
  return(implication_basis)
}


calculate_generic_base_convex_incidence_gurobi <- function(basic_formal_context, 
                                                           distance_matrix, 
                                                           maxdist,
                                                           binary = TRUE) {
  # Calculates basis function for context with points in R^2 as objects and 
  # half-spaces as inputs. It follows that all extents are convex sets and according
  # to Caratheodory's theorem (convex hull) it is sufficient to consider only
  # premises with three points in R^2
  # Furhtermore, we assume that only three points with a maximal distance of
  # maxdist can be selected as premises 
  
  # @basic_formal_context (list):  Contains the formal context, points as objects
  # @distance_matrix (matrix): distance matrix between the points (objects)
  # @maxdist (numeric): maximal distance between  three premises points
  # @binary (logical): if the it's an binary mixed linear problem
  
  # Output: gurobi_model
  
  ## erzeugt MILP Model ueber die Implementation von Contsraints, die das
  # Repsektieren der generischen (Gegenstands-) Implikationsbasis sicherstellen
  
  
  number_obj <- dim(basic_formal_context$context)[1]
  number_premises <- choose(number_obj,3)
  
  # Memory space to save the maximal distance between the premises
  max_distance_premis_points <- rep(0,number_premises)
  
  # Memory space for savin the further gurobi elements
  rhs <- rep(0, number_premises)
  sense <- rep(">=", number_premises)
  
  i_row <- list()
  j_column <- list()
  v_value <- list()

  
  # Memory space for saving
  indexs <- array(0,c(number_premises,3))
  count_implication <- 1
  
  
  # Three points are selected as premises, with further assumption that the distance
  # between the points is smaller than maxdist
  for (k in (1:(number_obj - 2))) {
    for (l in ((k + 1):(number_obj - 1))) {
      
      if (distance_matrix[k,l] <= maxdist) {
        for (m in ((l + 1):number_obj)) {
          
          if (distance_matrix[k,l] < maxdist & distance_matrix[m,l] <= maxdist) {
            # Defining the premise
            inner_premise <- rep(0,number_obj)
            inner_premise[c(k, l, m)] <- 1
            
            # Calculate the conclusion
            inner_premise_conclusion <- calculate_convex_conclusion_3point_premise(inner_premise, list(basic_formal_context = basic_formal_context))
            
            # we delete the trivial part: premise --> premise
            index_inner_premise <- which(inner_premise_conclusion$premise == 1)
            inner_premise_conclusion$conclusion[index_inner_premise] <- 0
            index_inner_conclusion <- which(inner_premise_conclusion$conclusion == 1)
            
            # Saving the maximal distance between premises points
            max_distance_premis_points[count_implication] <- max(distance_matrix[k,l],
                                                                 distance_matrix[k,m],
                                                                 distance_matrix[l,m])
            
            # Size of the conclusion
            size_conclusion <- length(index_inner_conclusion)
            size_premise <- length(index_inner_premise)
            if (size_conclusion > 0) { # Implication is not trivial
              
              # In the following a matrix will be defined, where each row reflects
              # a single implication. The columns represent the objects, when the object
              # is within the premise, we set the value to -1 and if its within the 
              # conclusion, we set it to 1/(number of elements within conclusion)

              # Saving the conclusion
              i_row <- append(i_row, rep(count_implication, size_conclusion))
              j_column <- append(j_column, index_inner_conclusion)
              v_value <- append(v_value, rep(-1/size_conclusion, size_conclusion))
              
              # Saving premise
              i_row <- append(i_row, rep(count_implication, size_premise))
              j_column <- append(j_column, index_inner_premise)
              v_value <- append(v_value, rep(1, size_premise))
              
              # Saving further gurobi elements
              sense[count_implication] <- ">=" 
          
              indexs[count_implication,] <- c(k,l,m)

              count_implication <- count_implication + 1
            }
          }
        }
      }
    }
  }
  
  # Test if all implications are redundant and if yes, replace constrains by a trivial one.
  # And return this object.
  if (length(i_row) == 0) {
    model <- list(A = array(rep(0, number_obj), dim = c(1,number_obj)),
                  obj = NULL,
                  modelsense = "max",
                  rhs = c(-1),
                  sense = c(">="),
                  vtypes = rep('B',number_obj),
                  D = max_distance_premis_points, # für was wird D und indexs gebraucht?
                  indexs = NULL)
    return(model)
  }
  
  i_row <- as.array(unlist(i_row))
  j_column <- as.array(unlist(j_column))
  v_value <- as.array(unlist(v_value))
  
  count_implication <- count_implication - 1
  # Starting the garbage collection
  gc()
  
  # Construction of the gurobi_model
  model <- list(A = simple_triplet_matrix(i = i_row, j = j_column, v = v_value),
                obj = NULL,
                modelsense = "max",
                rhs = rhs[(1:count_implication)],
                sense = sense[(1:count_implication)],
                vtypes = rep('B',number_obj),
                D = max_distance_premis_points, # für was wird D und indexs gebraucht?
                indexs = indexs)
  
  return(model)
}



calculate_gufimpl_spatial_sumgurobi <- function(basic_formal_context, 
                                                 distance_matrix, 
                                                 maxdist,
                                                 binary = TRUE) {
  # Calculates basis function for context with points in R^2 as objects and 
  # half-spaces as inputs. It follows that all extents are convex sets and according
  # to Caratheodory's theorem (convex hull) it is sufficient to consider only
  # premises with three points in R^2
  # Furthermore, we assume that only three points with a maximal distance of
  # maxdist can be selected as premises.
  
  # @basic_formal_context (list):  Contains the formal context, points as objects
  # @distance_matrix (matrix): distance matrix between the points (objects)
  # @maxdist (numeric): maximal distance between  three premises points
  # @binary (logical): if the it's an binary mixed linear problem
  # @calculate_conlcusion (func): Function to calculate the conclusion based on three points
  
  # Output (list): A - describes the family of implications
  #                length_premise - the length of the premise corresponding to the 
  #                                 rows of A
  #               REST - for gurobi calculation
  
 
  
  number_obj <- dim(basic_formal_context$context)[1]
  number_premises <- choose(number_obj,3)
  
  # Memory space to save the maximal distance between the premises
  max_distance_premis_points <- rep(0,number_premises)
  length_premise <- list()
  
  # Memory space for saving the parts to calculate a triple matrix
  i_row <- list()
  j_column <- list()
  v_value <- list()
  
  count_implication <- 1
  
  # Three points are selected as premises, with further assumption that the distance
  # between the points is smaller than maxdist
  for (k in (1:(number_obj - 2))) {
    for (l in ((k + 1):(number_obj - 1))) {
      
      if (distance_matrix[k,l] <= maxdist) {
        for (m in ((l + 1):number_obj)) {
          
          if (distance_matrix[k,l] < maxdist & distance_matrix[m,l] <= maxdist) {
            # Defining the premise
            inner_premise <- rep(0,number_obj)
            inner_premise[c(k, l, m)] <- 1
            
            # Calculate the conclusion
            inner_premise_conclusion <- calculate_convex_conclusion_3point_premise(inner_premise, list(basic_formal_context = basic_formal_context))
            
            # we delete the trivial part: premise --> premise
            index_inner_premise <- which(inner_premise_conclusion$premise == 1)
            inner_premise_conclusion$conclusion[index_inner_premise] <- 0
            index_inner_conclusion <- which(inner_premise_conclusion$conclusion == 1)
            
            # Saving the maximal distance between premises points
            max_distance_premis_points[count_implication] <- max(distance_matrix[k,l],
                                                                 distance_matrix[k,m],
                                                                 distance_matrix[l,m])
            
            # Size of the conclusion
            size_conclusion <- length(index_inner_conclusion)
            size_premise <- length(index_inner_premise)
            if (size_conclusion > 0) { # Implication is not trivial
              
              # In the following a matrix will be defined, where each row reflects
              # a single implication. The columns represent the objects, when the object
              # is within the premise, we set the value to -1 and if its within the 
              # conclusion, we set it to 1/(number of elements within conclusion
              
              
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
                  length_premise = c(0),
                  D = max_distance_premis_points)
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
                length_premise = length_premise,
                D = max_distance_premis_points)
  
  return(model)
}
  

################################################################################
# generator calculation
################################################################################
calculate_generator_convex <- function(subset, list_info){
  
  # Caclulates the generator of a subset given by the spatial formal context
  
  # @subset (vector of (0,1)): 1 represents that the point is within the 
  #                             subset
  # @list_info (list): contains the point_matrix of the observations
  
  # Output (list): all generators of the spatial closure of subset
  
  
  point_matrix <- list_info$point_matrix
  index_row_subset <- which(subset == 1)
  point_subset <- point_matrix[index_row_subset, ]
  
  # The generator corresponds to the convex hull of the subset
  index_convex_hull_subset <- chull(point_subset)
  
  index_chull <- index_row_subset[index_convex_hull_subset]
  generator <- rep(0, dim(point_matrix)[1])
  generator[index_chull] <- 1
  
  return(list(generator))
}

