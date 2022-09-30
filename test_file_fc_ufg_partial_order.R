################################################################################
# Test file
################################################################################

test_mat_1 <- matrix(rep(0,9), nrow = 3)
diag(test_mat_1) <- 1

test_mat_2 <- matrix(rep(0,9), nrow = 3)
diag(test_mat_2) <- 1
test_mat_2[1,2] <- 1
test_mat_2[3,2] <- 1

test_mat_3 <- matrix(rep(0,9), nrow = 3)
diag(test_mat_3) <- 1
test_mat_3[2,3] <- 1
test_mat_3[3,1] <- 1

test_mat_4 <- matrix(rep(0,9), nrow = 3)
diag(test_mat_4) <- rep(1,3)
test_mat_4[1,2] <- 1

ufg_test_1 <- list(test_mat_1, test_mat_2) 
ufg_test_2 <- list(test_mat_2, test_mat_3) 
ufg_test_3 <- list(test_mat_1, test_mat_4)
ufg_test_4 <- list(test_mat_3, test_mat_4)
ufg_test_5 <- list(test_mat_1)
ufg_test_6 <- list(test_mat_2, test_mat_2)


test_if_ufg_partial(ufg_test_1)
# [1] TRUE
test_if_ufg_partial(ufg_test_2)
# [1] TRUE
test_if_ufg_partial(ufg_test_3)
# [1] FALSE
test_if_ufg_partial(ufg_test_4)
# [1] TRUE
test_if_ufg_partial(ufg_test_5)
# FALSE
test_if_ufg_partial(ufg_test_6)
# [1] FALSE
