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


compute_relation_product <-function(X,Y){ 
  
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



# Daten einlesen und konvertieren (Hannahs Code)

library(prefmod)

data_col <- cemspc
data_col[,15] <- 2- data_col[,15]
View(data_col)
colnames(data_col)
which_have_nas <- which(rowSums(is.na(data_col)) > 0) # die ersten 91 Einträge


### Convert dataset


convert_to_matrix <- function(row_values, set_NA_to = NA) {
  # set_NA_to, can equal 0, 1, 2 or NA, 
  #   0: incomparable, 1: first is better, 2: second better
  
  # Result (list): Matrix wrapped up in a list with rows/columns refer to
  #       (1:"London", 2:"Paris", 3:"Milano", 4:"St. Gallen", 5:"Barcelona", 6:"Stockholm")
  
  
  graph_mat <- matrix(rep(-1, 6*6), nrow = 6)
  diag(graph_mat) <- 1
  
  comparison_index <- c(c(1,2), c(1,3), c(2,3), c(1,4), c(2,4), c(3,4),
                        c(1,5), c(2,5), c(3,5), c(4,5),
                        c(1,6), c(2,6), c(3,6), c(4,6), c(5,6))
  # vergleich dies mit der Definition von V1- V15 auf Seite 6 von
  # https://cran.r-project.org/web/packages/prefmod/prefmod.pdf
  
  for (i in 1:15) {
    if (is.na(row_values[i])) {
      graph_mat[comparison_index[i*2 - 1], comparison_index[i*2]] <- (set_NA_to %% 2) # modulo 2
      graph_mat[comparison_index[i*2], comparison_index[i*2 - 1]] <- max(set_NA_to - 1, 0)
    } else if (row_values[i] == 0) {
      graph_mat[comparison_index[i*2 - 1], comparison_index[i*2]] <- 1
      graph_mat[comparison_index[i*2], comparison_index[i*2 - 1]] <- 0
    } else if (row_values[i] == 1) {
      graph_mat[comparison_index[i*2 - 1], comparison_index[i*2]] <- 0
      graph_mat[comparison_index[i*2], comparison_index[i*2 - 1]] <- 0
    } else if (row_values[i] == 2) {
      graph_mat[comparison_index[i*2 - 1], comparison_index[i*2]] <- 0
      graph_mat[comparison_index[i*2], comparison_index[i*2 - 1]] <- 1
    } 
  }
  return(list(graph_mat))
}
# single_to_try <- convert_to_matrix(data_col[1,], set_NA_to = 0)
# three_to_try <- unlist(apply(data_col[c(1,2,3), ], 1, convert_to_matrix, set_NA_to = 0), recursive = FALSE)
# test_if_porder(single_to_try)

relations_incomp <- apply(data_col, 1, convert_to_matrix, set_NA_to = 0)
relations_first_better <- apply(data_col, 1, convert_to_matrix, set_NA_to = 1)
relations_second_better <- apply(data_col, 1, convert_to_matrix, set_NA_to = 2)



### test if these are partial orders (funktion findet man in fc_ufg_partial_order.R)
check_relation_po_incomp <- lapply(unlist(relations_incomp, recursive = FALSE), test_if_porder)
check_relation_po_first <- lapply(unlist(relations_first_better, recursive = FALSE), test_if_porder)
check_relation_po_second <- lapply(unlist(relations_second_better, recursive = FALSE), test_if_porder)
# die warnings können ignoriert werden, sind "Absicht"


which_po_incomp <- which(unlist(check_relation_po_incomp))
which_po_first <- which(unlist(check_relation_po_first))
which_po_second <- which(unlist(check_relation_po_second))

which_po_without_nas <- which_po_incomp[which_po_incomp > 91]
which_po_with_na_incomp_first <- Reduce(intersect, list(which_po_incomp[which_po_incomp < 92], which_po_first[which_po_first < 92])) # 1 12 13 23 27 32 33 35 43 68 71 78 82 85
which_po_with_na_incomp_second <- Reduce(intersect, list(which_po_incomp[which_po_incomp < 92], which_po_second[which_po_second < 92])) # 12 13 14 23 27 32 33 35 43 68 71 78 85
which_po_with_na_second_first <- Reduce(intersect, list(which_po_second[which_po_second < 92], which_po_first[which_po_first < 92])) # 12 13 23 27 32 33 35 43 68 71 78 85
which_po_with_na_incomp_first_second <- Reduce(intersect, list(which_po_incomp[which_po_incomp < 92], which_po_first[which_po_first < 92], which_po_second[which_po_second < 92])) # 12 13 23 27 32 33 35 43 68 71 78 85



# the final "datasets"

data_set_without_nas <- unlist(relations_incomp[which_po_without_nas], recursive = FALSE)

X<- cemspc[which_po_without_nas,c(16,17)]

orders <- data_set_without_nas
complemented_orders <- list()


for(k in (1:length(orders))){

colnames(orders[[k]]) <- rownames(orders[[k]]) <- c("London", "Paris", "Milano", "St. Gallen", "Barcelona", "Stockholm")

complemented_orders[[k]] <- cbind(orders[[k]],1-orders[[k]])
}



#########################################################################

##Test mit Tukeys_depth
nrep=10000
a=rep(0,nrep)
for(k in (1:nrep)){
i=sample((1:170))
i=(1:170)
orders1 <- orders[which(X[i,2]==1)]
orders2 <- orders[which(X[i,2]==2)]
context1 <- context[which(X[i,2]==1),]
context2 <- context[which(X[i,2]==2),]


complemented_orders1 <- complemented_orders[which(X[i,2]==1)]
complemented_orders2 <- complemented_orders[which(X[i,2]==2)]

TM1 <- Tukeys_geodetic_median_order(complemented_orders1,1.0,auto=TRUE,fraction=0.8)
TM2 <- Tukeys_geodetic_median_order(complemented_orders2,1.0,auto=TRUE,fraction=0.8)

#TM_diff <- Tukeys_true_median_difference(complemented_orders1,complemented_orders2)
#TM_diff

#plot(as.relation(TM1[,(1:6)]))
#dev.new()
#plot(as.relation(TM2[,(1:6)]))


T = Tukeys_depth(rbind(as.vector(TM1),context2),weights=c(0,rep(1,nrow(context2))))[1]

T= min(T, Tukeys_depth(rbind(as.vector(TM2),context1),weights=c(0,rep(1,nrow(context1))))[1])


print(T)

a[k] <- T
print(mean(a[(1:k)]<=T_obs))

}



m <- length(orders)
leq_context <- NULL
for(k in (1:m)){leq_context <- rbind(leq_context,as.vector(orders[[k]]))}


context <- cbind(leq_context,1-leq_context)

TD <- Tukeys_depth(context)
i_TD <- which.max(PD)

mode_TD <- context[i_TD,(1:36)];dim(mode_TD) <- c(6,6);rownames(mode_TD)<- colnames(mode_TD)<-c("London", "Paris", "Milano", "St. Gallen", "Barcelona", "Stockholm")

plot(as.relation(t(mode_TD)))



PD <- rep(0,170)
for(k in (1:100)){
i <- sample((1:170));PD[i] <- PD[i] + peeling_depth(context[i,])
print(k)}

i_PD <- which.max(PD)

mode_PD <- context[i_PD,(1:36)];dim(mode_PD) <- c(6,6);rownames(mode_PD)<- colnames(mode_PD)<-c("London", "Paris", "Milano", "St. Gallen", "Barcelona", "Stockholm")

plot(as.relation(t(mode_PD)))


RD <- random_depth(context,K=10,nrep=10000)

i_RD <- which.max(RD)

mode_RD <- context[i_RD,(1:36)];dim(mode_RD) <- c(6,6);rownames(mode_RD)<- colnames(mode_RD)<-c("London", "Paris", "Milano", "St. Gallen", "Barcelona", "Stockholm")

plot(as.relation(t(mode_RD)))




