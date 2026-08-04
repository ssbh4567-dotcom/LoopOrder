#' Likelihood Ratio Test for Simple Loop Order Alternatives
#'
#' Performs a likelihood ratio test (LRT) for testing equality of means
#' across multiple groups against the simple loop-order alternative
#' \eqn{\mu_1 \le \mu_i \le \mu_k} for \eqn{i = 2, \ldots, k-1}.
#' The test compares the null hypothesis of equal means across all groups
#' with an ordered alternative where the middle groups lie between
#' the first and the last group means.
#'
#' @param MUU A numeric vector of sample means for the groups.
#' @param VAR A numeric vector of biased sample variances (unrestricted MLE) for each group.
#' @param Sam_size A numeric vector of sample sizes for each group.
#' @param significance_level A numeric value in (0,1) specifying the
#'   significance level (e.g., \code{0.05}).
#' @param n.boot Number of bootstrap replications (default = \code{100000}).
#' @param seed Optional random seed for reproducibility.
#'
#' @return A list containing:
#'   \item{critical_value}{Bootstrap critical value at the specified level}
#'   \item{lrt_statistic}{Observed LRT statistic}
#'   \item{p_value}{Bootstrap p-value}
#'   \item{decision}{Test decision}
#'
#' @details
#' The test evaluates:
#' \deqn{
#'   H_0:\; \mu_1 = \mu_2 = \cdots = \mu_k
#'   \qquad \text{vs.} \qquad
#'   H_1:\; \mu_1 \le \mu_i \le \mu_k,\; i = 2,\ldots,k-1.
#' }
#'
#' The LRT statistic is computed from the ratio of maximized likelihoods
#' under the null and under the loop-order restriction. Parametric bootstrap
#' sampling from \eqn{N(0,\sigma_i^2)} is used to obtain critical values
#' and p-values.
#'
#' @importFrom stats quantile rnorm var
#' @importFrom Iso pava
#' @export
#'
#' @author Subha Halder
#'
#' @examples
#' M <- c(0.2, 0.8, 0.5, 1.2)
#' V <- c(1.5, 2.9, 4.0, 1.3)
#' n <- c(20, 22, 25, 18)
#' LoopLRT(M, V, n, significance_level = 0.05, n.boot = 1000)
#' \donttest{
#' # Recommended: Use 100000
#' LoopLRT(M, V, n, significance_level = 0.05, n.boot = 100000)
#' }
LoopLRT <- function(MUU, VAR, Sam_size, significance_level, n.boot = 100000, seed = NULL) {
  if (!is.null(seed)) {
    set.seed(seed)
  }
  if (!is.numeric(significance_level) || significance_level <= 0 || significance_level >= 1) {
    stop("significance_level must be a number in (0,1).")
  }
  if (!(length(MUU) == length(VAR) && length(VAR) == length(Sam_size))) {
    stop("MUU, VAR and Sam_size must have the same length.")
  }
  num_datasets <- length(Sam_size)
  if (num_datasets < 3) stop("Function requires at least 3 groups (num_datasets >= 3).")
  Loop_MLE <- function(X, n) {
    X1 <- X[-1]
    n1 <- n[-1]
    X2 <- X1[-length(X1)]
    n2 <- n1[-length(X1)]
    sorted_indices <- order(X2)
    X2_sorted <- X2[sorted_indices]
    n2_sorted <- n2[sorted_indices]
    new_X <- c(X[1],X2_sorted,X[length(X)])
    new_n <- c(n[1],n2_sorted,n[length(X)])
    mod_X <- pava(new_X,new_n)
    mod_X1 <- mod_X[-1]
    mod_X2 <- mod_X1[-length(mod_X1)]
    mod_X2_rearranged <- numeric(length(mod_X2))
    mod_X2_rearranged[sorted_indices] <- mod_X2
    loop_X <- c(mod_X[1], mod_X2_rearranged ,mod_X[length(X)])
    return(loop_X)
  }
  LRT_H0_loop_new <- function(means, var, sample_sizes) {
    old_Mu0 <- means
    old_var0 <- var

    mu1 <- sum(means*sample_sizes)/sum(sample_sizes)
    u1 <- sample_sizes / old_var0
    repeat {
      new_mu1 <- sum(old_Mu0 * u1) / sum(u1)
      new_var1 <- old_var0 + (new_mu1 - old_Mu0)^2
      new_u1 <- sample_sizes / new_var1

      if (max(abs(new_mu1 - mu1)) <= 0.0000001) {
        u1 <- new_u1
        mu1 <- new_mu1
        var1 <- new_var1
        break  # Exit the loop if the difference is less than epsilon
      }

      u1 <- new_u1
      mu1 <- new_mu1
      var1 <- new_var1
    }
    return(var1)
  }
  LRT_H1_loop_new <- function(mu0, var0, n) {
    w0 <- n / var0
    old_Mu0 <- mu0
    old_var0 <- var0
    repeat {
      new_mu0 <- Loop_MLE(old_Mu0, w0)
      new_var0 <- old_var0 + (new_mu0 - old_Mu0)^2
      new_w0 <- n/new_var0
      if (max(abs(new_mu0 - mu0)) <= 0.0000001) {
        w0 <- new_w0
        mu0 <- new_mu0
        var0 <- new_var0
        break
      }
      w0 <- new_w0
      mu0 <- new_mu0
      var0 <- new_var0
    }
    return(var0)
  }
  num_samples <- n.boot
  n <- Sam_size
  Unb_var <- (n/(n-1))*VAR
  lambda_values_star <- numeric(num_samples)
  var_H1_obs <- LRT_H1_loop_new(MUU, VAR, n)
  var_H0_obs <- LRT_H0_loop_new(MUU, VAR, n)
  V_R_obs <- var_H1_obs / var_H0_obs
  weights_obs <- sapply(1:num_datasets, function(i) V_R_obs[i]^(n[i] / 2))
  lambda <- prod(weights_obs)

  for (i in 1:num_samples) {
    boot_means <- numeric(num_datasets)
    boot_vars <- numeric(num_datasets)
    for (j in 1:num_datasets) {
      boot_data <- rnorm(n = n[j], mean = 0, sd = sqrt(Unb_var[j]))
      boot_means[j] <- mean(boot_data)
      boot_vars[j] <- sum((boot_data - boot_means[j])^2) / n[j]
    }
    var_H1_star <- LRT_H1_loop_new(boot_means, boot_vars, n)
    var_H0_star <- LRT_H0_loop_new(boot_means, boot_vars, n)
    V_R_star <- var_H1_star / var_H0_star
    weights_star <- sapply(1:num_datasets, function(j)
      V_R_star[j]^(n[j] / 2))
    lambda_values_star[i] <- prod(weights_star)
  }
  quantile_value <- quantile(lambda_values_star, probs = significance_level)
  p_value <- mean(lambda_values_star <= lambda)
  if (lambda < quantile_value) {
    result <- "Reject null hypothesis"
  } else {
    result <- "Do not reject null hypothesis"
  }

  # Output
  return(paste(
    "Critical value:", quantile_value,
    "; LRT statistic:", lambda,
    "; p-value:", p_value,
    "; Result:", result
  ))
}



#' LoopMax (maximum of test statistic based) Test for Simple Loop Order Alternatives
#'
#' Performs the LoopMax test for assessing equality of means across multiple
#' groups against the simple loop‐order alternative
#' \eqn{\mu_1 \le \mu_i \le \mu_k} for \eqn{i = 2, \ldots, k-1}.
#' The test compares the null hypothesis of equal means with an ordered
#' alternative in which the interior group means lie between the first and last
#' group means.
#'
#' @param MUU A numeric vector of sample means for the groups.
#' @param VAR A numeric vector of biased sample variances (unrestricted MLE)
#'   for each group.
#' @param Sam_size A numeric vector of sample sizes for each group.
#' @param significance_level A numeric value in (0,1) specifying the significance
#'   level (e.g., \code{0.05}).
#' @param n.boot Number of bootstrap replications (default = \code{100000}).
#' @param seed Optional random seed for reproducibility.
#'
#' @return A list containing:
#'   \item{critical_value}{Bootstrap critical value at the specified level}
#'   \item{max_statistic}{Observed LoopMax test statistic}
#'   \item{p_value}{Bootstrap p-value}
#'   \item{decision}{Test decision}
#'
#' @details
#' The test evaluates:
#' \deqn{
#'   H_0:\; \mu_1 = \mu_2 = \cdots = \mu_k
#'   \qquad \text{vs.} \qquad
#'   H_1:\; \mu_1 \le \mu_i \le \mu_k,\; i = 2,\ldots,k-1.
#' }
#'
#' The LoopMax statistic is constructed by comparing each interior group mean
#' to the boundary groups, standardized by the pooled variance estimate. Then take maximum of the differences.
#' A parametric bootstrap based on
#' \eqn{N(0, \sigma_i^2)} is used to obtain critical values
#' and p-values.
#'
#' @importFrom stats quantile rnorm var
#' @export
#'
#' @author Subha Halder
#'
#' @examples
#' M <- c(0.2, 0.8, 0.5, 1.2)
#' V <- c(1.5, 2.9, 4.0, 1.3)
#' n <- c(20, 22, 25, 18)
#' LoopMax(M, V, n, significance_level = 0.05, n.boot = 1000)
#' \donttest{
#' # Recommended: Use 100000
#' LoopMax(M, V, n, significance_level = 0.05, n.boot = 100000)
#' }
#'
LoopMax <- function(MUU, VAR, Sam_size, significance_level, n.boot = 100000, seed = NULL) {
  if (!is.null(seed)) set.seed(seed)
  if (!is.numeric(significance_level) || significance_level <= 0 || significance_level >= 1) {
    stop("significance_level must be a number in (0,1).")
  }
  if (!(length(MUU) == length(VAR) && length(VAR) == length(Sam_size))) {
    stop("MUU, VAR and Sam_size must have the same length.")
  }
  num_datasets <- length(Sam_size)
  if (num_datasets < 3) stop("Function requires at least 3 groups (num_datasets >= 3).")
  num_samples <- n.boot
  n <- Sam_size
  vars <- (n/(n-1))*VAR
  T_max <- numeric(num_samples)

  for (u in 1:num_samples) {
    bootstrap_samples <- vector("list", num_datasets)
    for (j in 1:num_datasets) {
      bootstrap_samples[[j]] <- rnorm(n = n[j], mean = 0, sd = sqrt(vars[j]))
    }
    D_star_max1 <- max(
      sapply(2:(num_datasets-1), function(i) {
        (mean(bootstrap_samples[[i]]) - mean(bootstrap_samples[[1]])) /
          sqrt(
            (var(bootstrap_samples[[i]]) / length(bootstrap_samples[[i]])) +
              (var(bootstrap_samples[[1]]) / length(bootstrap_samples[[1]])))
      }))


    D_star_max2 <-max(
      sapply(2:(num_datasets-1), function(i) {
        (-mean(bootstrap_samples[[i]]) + mean(bootstrap_samples[[num_datasets]])) /
          sqrt(
            (var(bootstrap_samples[[i]]) / length(bootstrap_samples[[i]])) +
              (var(bootstrap_samples[[num_datasets]]) / length(bootstrap_samples[[num_datasets]])))
      }))

    T_max[u] <- max(D_star_max1,D_star_max2)
  }

  Dm_values1 <- max(
    sapply(2:(num_datasets-1), function(i) {
      (MUU[i] - MUU[1]) / sqrt((vars[i] / n[i]) + (vars[1] / n[1]))
    }))

  Dm_values2 <- max(sapply(2:(num_datasets-1), function(i) {
    (-MUU[i] + MUU[num_datasets]) / sqrt((vars[i] / n[i]) + (vars[num_datasets] / n[num_datasets]))
  }))

  Tm_values <- max(Dm_values1,Dm_values2)

  quantile_value <- quantile(T_max, probs = 1 - significance_level, na.rm = TRUE)
  p_value <- mean(T_max >= Tm_values, na.rm = TRUE)

  # Decision
  if (Tm_values > quantile_value) { result <- "Reject null hypothesis" }
  else { result <- "Do not reject null hypothesis" }

  # Output summary
  return(paste(
    "Critical value:", quantile_value,
    "; LoopMax Test statistic:", Tm_values,
    "; p-value:", p_value,
    "; Result:", result
  ))
}


#' LoopMin (minimum of test statistic based) Test for Simple Loop Order Alternatives
#'
#' Performs the LoopMin test for assessing equality of means across multiple
#' groups against the simple loop‐order alternative
#' \eqn{\mu_1 \le \mu_i \le \mu_k} for \eqn{i = 2, \ldots, k-1}.
#' The test compares the null hypothesis of equal means with an ordered
#' alternative in which the interior group means lie between the first and last
#' group means.
#'
#' @param MUU A numeric vector of sample means for the groups.
#' @param VAR A numeric vector of biased sample variances (unrestricted MLE)
#'   for each group.
#' @param Sam_size A numeric vector of sample sizes for each group.
#' @param significance_level A numeric value in (0,1) specifying the significance
#'   level (e.g., \code{0.05}).
#' @param n.boot Number of bootstrap replications (default = \code{100000}).
#' @param seed Optional random seed for reproducibility.
#'
#' @return A list containing:
#'   \item{critical_value}{Bootstrap critical value at the specified level}
#'   \item{max_statistic}{Observed LoopMin test statistic}
#'   \item{p_value}{Bootstrap p-value}
#'   \item{decision}{Test decision}
#'
#' @details
#' The test evaluates:
#' \deqn{
#'   H_0:\; \mu_1 = \mu_2 = \cdots = \mu_k
#'   \qquad \text{vs.} \qquad
#'   H_1:\; \mu_1 \le \mu_i \le \mu_k,\; i = 2,\ldots,k-1.
#' }
#'
#' The LoopMin statistic is constructed by comparing each interior group mean
#' to the boundary groups, standardized by the pooled variance estimate. Then take minimum of the differences.
#' A parametric bootstrap based on
#' \eqn{N(0, \sigma_i^2)} is used to obtain critical values
#' and p-values.
#'
#' @importFrom stats quantile rnorm var
#' @export
#'
#' @author Subha Halder
#'
#' @examples
#' M <- c(0.2, 0.8, 0.5, 1.2)
#' V <- c(1.5, 2.9, 4.0, 1.3)
#' n <- c(20, 22, 25, 18)
#' LoopMin(M, V, n, significance_level = 0.05, n.boot = 1000)
#' \donttest{
#' # Recommended: Use 100000
#' LoopMin(M, V, n, significance_level = 0.05, n.boot = 100000)
#' }
LoopMin <- function(MUU, VAR, Sam_size, significance_level, n.boot = 100000, seed = NULL) {
  if (!is.null(seed)) set.seed(seed)
  if (!is.numeric(significance_level) || significance_level <= 0 || significance_level >= 1) {
    stop("significance_level must be a number in (0,1).")
  }
  if (!(length(MUU) == length(VAR) && length(VAR) == length(Sam_size))) {
    stop("MUU, VAR and Sam_size must have the same length.")
  }
  num_datasets <- length(Sam_size)
  if (num_datasets < 3) stop("Function requires at least 3 groups (num_datasets >= 3).")
  num_samples <- n.boot
  n <- Sam_size
  vars <- (n/(n-1))*VAR
  T_min <- numeric(num_samples)

  for (u in 1:num_samples) {
    bootstrap_samples <- vector("list", num_datasets)
    for (j in 1:num_datasets) {
      bootstrap_samples[[j]] <- rnorm(n = n[j], mean = 0, sd = sqrt(vars[j]))
    }
    D_star_min1 <- max(
      sapply(2:(num_datasets-1), function(i) {
        (mean(bootstrap_samples[[i]]) - mean(bootstrap_samples[[1]])) /
          sqrt(
            (var(bootstrap_samples[[i]]) / length(bootstrap_samples[[i]])) +
              (var(bootstrap_samples[[1]]) / length(bootstrap_samples[[1]])))
      }))


    D_star_min2 <-max(
      sapply(2:(num_datasets-1), function(i) {
        (-mean(bootstrap_samples[[i]]) + mean(bootstrap_samples[[num_datasets]])) /
          sqrt(
            (var(bootstrap_samples[[i]]) / length(bootstrap_samples[[i]])) +
              (var(bootstrap_samples[[num_datasets]]) / length(bootstrap_samples[[num_datasets]])))
      }))

    T_min[u] <- min(D_star_min1,D_star_min2)
  }

  Dm_values1 <- max(
    sapply(2:(num_datasets-1), function(i) {
      (MUU[i] - MUU[1]) / sqrt((vars[i] / n[i]) + (vars[1] / n[1]))
    }))

  Dm_values2 <- max(sapply(2:(num_datasets-1), function(i) {
    (-MUU[i] + MUU[num_datasets]) / sqrt((vars[i] / n[i]) + (vars[num_datasets] / n[num_datasets]))
  }))

  Tm_values <- min(Dm_values1,Dm_values2)

  quantile_value <- quantile(T_min, probs = 1 - significance_level, na.rm = TRUE)
  p_value <- mean(T_min >= Tm_values, na.rm = TRUE)

  # Decision
  if (Tm_values > quantile_value) { result <- "Reject null hypothesis" }
  else { result <- "Do not reject null hypothesis" }

  # Output summary
  return(paste(
    "Critical value:", quantile_value,
    "; LoopMin Test statistic:", Tm_values,
    "; p-value:", p_value,
    "; Result:", result
  ))
}







