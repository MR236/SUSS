library(survival)
library(tidyverse)
library(splines)
library(splines2)
library(intccr)
library(pseudo)
library(survminer)
library(rmutil)

hybrid_integration <- function(f, lower, upper, disconts=NULL, pivot=lower) {
  if (pivot == lower) {return(int(f, lower, upper))}
  ord <- order(upper)
  upper <- upper[ord]
  partA <- c(upper[upper<=pivot], pivot)
  integrals <- NULL
  for (i in partA) {
    partition <- c(lower, disconts[disconts<i & disconts>lower], i)
    integral <- 0
    for (j in seq(2, length(partition))) {
      integral <- integral + integrate(f, partition[j-1], partition[j])$value
    }
    integrals <- c(integrals, integral)
  }
  low_part <- integrals[length(integrals)]
  integrals <- integrals[-length(integrals)]
  partB <- upper[upper>pivot]
  PB_int <- rmutil::int(f, pivot, partB) + c(low_part)
  result <- c(integrals, PB_int)
  return(result[order(ord)])
}

fast_hybrid_integration <- function(f, lower, upper, pivot=lower) {
  if (pivot == lower) {return(int(f, lower, upper))}
  ord <- order(upper)
  upper <- upper[ord]
  partA <- c(lower, upper[upper<=pivot], pivot)
  integrals <- NULL
  integral <- 0
  for (i in seq(2, length(partA))) {
    integral <- integral + integrate(f, partA[i-1], partA[i])$value
    integrals <- c(integrals, integral)
  }
  low_part <- integrals[length(integrals)]
  integrals <- integrals[-length(integrals)]
  partB <- upper[upper>pivot]
  PB_int <- rmutil::int(f, pivot, partB) + c(low_part)
  result <- c(integrals, PB_int)
  return(result[order(ord)])
}


NelsonAalen_CH <- function(Delta,Times,time_point, weights=rep(1, length(Times))){
  t_j <- unique(Times[Times <= time_point])
  CH_estimate <- 0
  for (i in t_j) {
    events <- sum(weights*Delta*I(Times==i))
    at_risk <- sum(weights*I(Times>=i))
    CH_estimate <- CH_estimate+events/at_risk
  }
  return(CH_estimate)
}

KM_Estimate <- function(Delta, Times, time_point, weights=rep(1, length(Times))){
  t_j <- unique(Times[Times <= time_point])
  KM_estimate <- 1
  for (i in t_j) {
    events <- sum(weights*Delta*I(Times==i))
    at_risk <- sum(weights*I(Times>=i))
    KM_estimate <- KM_estimate*(1-events/at_risk)
  }
  return(KM_estimate)
}

NelsonAalen_Grad_CH <- function(Delta,Times,time_point, weights=rep(1, length(Times))){
  t_j <- unique(Times[Times <= time_point])
  CH_Grad <- rep(0, length(Times))
  for (i in t_j) {
    positive_part <- Delta*I(Times==i) / sum(weights*I(Times>=i))
    negative_part <- (sum(Delta*I(Times==i)*weights) / (sum(weights*I(Times>=i)))^2)*I(Times>=i)
    CH_Grad <- CH_Grad + positive_part - negative_part
  }
  return(CH_Grad)
}

NelsonAalen_Taylor_Pseudo <- function(Delta,Times,time_point, weights=rep(1, length(Times))){
  Gradient <- NelsonAalen_Grad_CH(Delta,Times,time_point, weights)
  Value <- NelsonAalen_CH(Delta,Times,time_point,weights)
  N <- length(Times)
  PV <- (N - 1) * (Gradient * weights) + rep(Value, N)
  return(PV)
}

NelsonAalen_Jackknife_Pseudo <- function(Delta,Times,time_point, weights=rep(1, length(Times))) {
  PV <- NULL
  CH <- NelsonAalen_CH(Delta,Times,time_point,weights)
  N <- length(Times)
  for (i in seq(1, N)) {
    Delta_New <- Delta[-i]
    Times_New <- Times[-i]
    Weights_New <- weights[-i]
    CH_jack <- NelsonAalen_CH(Delta_New,Times_New,time_point,Weights_New)
    PV <- c(PV, N*CH - (N-1)*CH_jack)
  }
  return(PV)
}

KaplanMeier_Taylor_Pseudo <- function(Delta,Times,time_point, weights=rep(1, length(Times))){
  Gradient <- NelsonAalen_Grad_CH(Delta,Times,time_point, weights)
  CH_Value <- NelsonAalen_CH(Delta,Times,time_point,weights)
  KM_Value <- KM_Estimate(Delta, Times, time_point, weights)
  N <- length(Times)
  PV <- -(N - 1) * (Gradient * weights)*exp(-CH_Value) + rep(KM_Value, N)
  return(PV)
}

get_time_quantiles <- function(t, s_t, qs) {
  quantiles <- NULL
  for (i in qs) {
    quantiles <- c(quantiles, max(t[which(s_t >= i)]))
  }
  return(quantiles)
}

# we want to vectorize at some point
numeric_inverse <- function (f, s, lower = 0, upper = 100) {
  return(as.numeric(uniroot((function (x) f(x) - s), lower = lower, upper = upper)[1]))
}

ms <- function(knots, k, x, i) {
  if (k == 1) {
    if (I(knots[i] <= x)*I(x < knots[i+1]) == 1) {return(1/(knots[i+1]-knots[i]))}
    else{return(0)}
  }
  else {
    rec1 <- ms(knots,k-1, x, i)
    rec2 <- ms(knots, k-1, x, i+1)
    numerator <- k*((x-knots[i])*rec1 + (knots[i+k]-x)*rec2)
    high <- i+k
    low <- i
    if (i < length(knots)/2) {while (knots[high]-knots[low]==0) {high <- high+1}}
    else{while (knots[high]-knots[low]==0) {low <- low-1}}
    denominator <- (k-1)*(knots[high]-knots[low])
    return(numerator/denominator)
  }
}

ms_x <- function(knots, k, x) {
  n <- length(knots)
  knots <- c(rep(knots[1], k), knots[2:(n-1)], rep(knots[n], k))
  n2 <- length(knots)
  row <- NULL
  for (i in c(1:(n2-k))){
    row <- c(row, ms(knots, k, x, i))
  }
  return(row)
}

expit <- function(eta){return(exp(eta)/(1 + exp(eta)))}
cloglog_inv <- function(eta){return(1 - exp(-exp(eta)))}
cloglog_inv_deriv <- function(eta){return(exp(eta-exp(eta)))}

survival_function <- function(t, knots, degree, boundary_knots, coefficients) {
  t <- ifelse(t>= boundary_knots[2], boundary_knots[2], t)
  basis <- cbind(rep(1, length(t)), iSpline(t, knots=knots, degree=degree, Boundary.knots = boundary_knots))
  return(expit(coefficients %*% t(basis)))
}

hazard_function <- function(t, knots, degree, boundary_knots, coefficients) {
  t <- ifelse(t>= boundary_knots[2], boundary_knots[2], t)
  S_T <- survival_function(t, knots, degree, boundary_knots, coefficients)
  dbasis <- cbind(rep(0, length(t)), mSpline(t, knots=knots, degree=degree, Boundary.knots = boundary_knots))
  basis <- cbind(rep(1, length(t)), iSpline(t, knots=knots, degree=degree, Boundary.knots = boundary_knots))
  term1 <- exp(coefficients %*% t(basis)) / (1+ exp(coefficients %*% t(basis)))^2
  term2 <- coefficients %*% t(dbasis)
  haz <- -term1*term2/S_T
  haz <- ifelse(haz <= 0, 0, haz)
  return(haz)
}


survival_function_cloglog <- function(t, knots, degree, boundary_knots, coefficients) {
  final_knot <- knots[length(knots)]
  if (t < knots[1]) {
    S_T1 <- survival_function_cloglog(knots[1], knots, degree, boundary_knots, coefficients)
    lambda <- -log(S_T1)/knots[1]
    return(exp(-t*lambda))
  }
  else if (t > final_knot) {
    lambda <- hazard_function_cloglog(final_knot, knots, degree, boundary_knots, coefficients)
    inc_t <- t - final_knot
    return(exp(-inc_t*lambda)*survival_function_cloglog(final_knot, knots, degree, boundary_knots, coefficients))
  }
  else {
    basis <- cbind(rep(1, length(t)), iSpline(t, knots=knots, degree=degree, Boundary.knots = boundary_knots))
    return(cloglog_inv(coefficients %*% t(basis)))
  }
}

survival_function_cloglog.v <- function(t, knots, degree, boundary_knots, coefficients, restriction = 0) {
  final_knot <- boundary_knots[2]
  first_knot <- max(boundary_knots[1], restriction)
  basis_T1 <- c(1, iSpline(first_knot, knots=knots, degree=degree, Boundary.knots=boundary_knots))
  S_T1 <- cloglog_inv(coefficients %*% basis_T1)
  lambda_T1 <- -log(S_T1) / first_knot
  basis_TF <- c(1, iSpline(final_knot, knots=knots, degree=degree, Boundary.knots=boundary_knots))
  dbasis_TF <- c(0, mSpline(final_knot, knots=knots, degree=degree, Boundary.knots=boundary_knots, intercept=TRUE))
  S_TF <- cloglog_inv(coefficients %*% basis_TF)
  term1_TF <- cloglog_inv_deriv(coefficients %*% basis_TF)
  term2_TF <- coefficients %*% dbasis_TF
  haz_TF <- -term1_TF*term2_TF/S_TF
  haz_TF <- ifelse(haz_TF <= 0, 0, haz_TF)
  basis_all <-  cbind(rep(1, length(t)), iSpline(t, knots=knots, degree=degree, Boundary.knots = boundary_knots))
  est_1 <- exp(-t*c(lambda_T1))
  est_2 <- exp((final_knot-t)*c(haz_TF))*c(S_TF)
  est_3 <- cloglog_inv(coefficients %*% t(basis_all))
  #final_est <- est_3
  #final_est <- ifelse(t > final_knot, est_2, est_3)
  final_est <- ifelse(t < first_knot, est_1, ifelse(t > final_knot, est_2, est_3))
  return(final_est)
}

hazard_function_cloglog.v <- function(t, knots, degree, boundary_knots, coefficients, restriction=0) {
  final_knot <- boundary_knots[2]
  first_knot <- max(boundary_knots[1], restriction)
  basis_T1 <- c(1, iSpline(first_knot, knots=knots, degree=degree, Boundary.knots=boundary_knots))
  S_T1 <- cloglog_inv(coefficients %*% basis_T1)
  lambda_T1 <- -log(S_T1) / first_knot
  basis_TF <- c(1, iSpline(final_knot, knots=knots, degree=degree, Boundary.knots=boundary_knots))
  dbasis_TF <- c(0, mSpline(final_knot, knots=knots, degree=degree, Boundary.knots=boundary_knots, intercept=TRUE))
  S_TF <- cloglog_inv(coefficients %*% basis_TF)
  term1_TF <- cloglog_inv_deriv(coefficients %*% basis_TF)
  term2_TF <- coefficients %*% dbasis_TF
  haz_TF <- -term1_TF*term2_TF/S_TF
  haz_TF <- ifelse(haz_TF <= 0, 0, haz_TF)
  S_T_all <- survival_function_cloglog.v(t, knots, degree, boundary_knots, coefficients)
  dbasis <- cbind(rep(0, length(t)), mSpline(t, knots=knots, degree=degree, Boundary.knots = boundary_knots, intercept=TRUE, periodic=FALSE))
  basis <- cbind(rep(1, length(t)), iSpline(t, knots=knots, degree=degree, Boundary.knots = boundary_knots))
  term1 <- cloglog_inv_deriv(coefficients %*% t(basis))
  term2 <- coefficients %*% t(dbasis)
  haz <- -term1*term2/S_T_all
  haz <- ifelse(haz <= 0, 0, haz)
  #final_haz <- haz
  #final_haz <- ifelse(t > final_knot, haz_TF, haz)
  final_haz <- ifelse(t < first_knot, lambda_T1, ifelse(t > final_knot, haz_TF, haz))
  return(final_haz)
}

variance_cloglog <- function(t_k, spline_params, restriction=0) {
  PHF.v <- function(t) {hazard_function_cloglog.v(t, spline_params$Event$Knots,
                                                  spline_params$Event$Degree, spline_params$Event$BKnots,
                                                  spline_params$Event$Coefficients)}
  
  PSF.v <- function(t) {survival_function_cloglog.v(t, spline_params$Event$Knots,
                                                    spline_params$Event$Degree, spline_params$Event$BKnots,
                                                    spline_params$Event$Coefficients)}
  PRF.v <- function(t) {survival_function_cloglog.v(t, spline_params$Risk$Knots,
                                                    spline_params$Risk$Degree, spline_params$Risk$BKnots,
                                                    spline_params$Risk$Coefficients)}
  term1 <- 1/(c(spline_params$N)*log(PSF.v(t_k))^2)
  integrand <- function(t) {
    return(PHF.v(t)/(PRF.v(t)*(1-PHF.v(t))))
  }
  term2 <- hybrid_integration(integrand, 0, t_k, disconts = NULL, pivot=restriction)
  return(term1*term2)
}

log_rank_numerator <- function(spline_params_all, spline_params_group1, restriction=0) {
  PHF.v <- function(t) {hazard_function_cloglog.v(t, spline_params_all$Event$Knots,
                                                  spline_params_all$Event$Degree, spline_params_all$Event$BKnots,
                                                  spline_params_all$Event$Coefficients)}
  PRF.v <- function(t) {survival_function_cloglog.v(t, spline_params_all$Risk$Knots,
                                                    spline_params_all$Risk$Degree, spline_params_all$Risk$BKnots,
                                                    spline_params_all$Risk$Coefficients)}
  PSF1.v <- function(t) {survival_function_cloglog.v(t, spline_params_group1$Event$Knots,
                                                     spline_params_group1$Event$Degree, spline_params_group1$Event$BKnots,
                                                     spline_params_group1$Event$Coefficients)}
  PHF1.v <- function(t) {hazard_function_cloglog.v(t, spline_params_group1$Event$Knots,
                                                   spline_params_group1$Event$Degree, spline_params_group1$Event$BKnots,
                                                   spline_params_group1$Event$Coefficients)}
  PRF1.v <- function(t) {survival_function_cloglog.v(t, spline_params_group1$Risk$Knots,
                                                     spline_params_group1$Risk$Degree, spline_params_group1$Risk$BKnots,
                                                     spline_params_group1$Risk$Coefficients)}
  risk_integrand <- function(t) {
    return(PRF1.v(t)*PHF.v(t))
  }
  observed_integrand <- function(t){
    return(PRF1.v(t)*PHF1.v(t))
  }
  expected1 <- spline_params_group1$N*hybrid_integration(risk_integrand, 0, spline_params_group1$Max, disconts = NULL, pivot=restriction)
  observed1 <- spline_params_group1$N*hybrid_integration(observed_integrand, 0, spline_params_group1$Max, disconts = NULL, pivot=restriction)
  return(observed1 - expected1)
}

log_rank_test <- function(spline_params_all, spline_params_group1, spline_params_group2, restriction=0) {
  PHF.v <- function(t) {hazard_function_cloglog.v(t, spline_params_all$Event$Knots,
                                                  spline_params_all$Event$Degree, spline_params_all$Event$BKnots,
                                                  spline_params_all$Event$Coefficients)}
  PRF.v <- function(t) {survival_function_cloglog.v(t, spline_params_all$Risk$Knots,
                                                    spline_params_all$Risk$Degree, spline_params_all$Risk$BKnots,
                                                    spline_params_all$Risk$Coefficients)}
  PSF1.v <- function(t) {survival_function_cloglog.v(t, spline_params_group1$Event$Knots,
                                                   spline_params_group1$Event$Degree, spline_params_group1$Event$BKnots,
                                                   spline_params_group1$Event$Coefficients)}
  PHF1.v <- function(t) {hazard_function_cloglog.v(t, spline_params_group1$Event$Knots,
                                                  spline_params_group1$Event$Degree, spline_params_group1$Event$BKnots,
                                                  spline_params_group1$Event$Coefficients)}
  PRF1.v <- function(t) {survival_function_cloglog.v(t, spline_params_group1$Risk$Knots,
                                                    spline_params_group1$Risk$Degree, spline_params_group1$Risk$BKnots,
                                                    spline_params_group1$Risk$Coefficients)}
  PSF2.v <- function(t) {survival_function_cloglog.v(t, spline_params_group2$Event$Knots,
                                                   spline_params_group2$Event$Degree, spline_params_group2$Event$BKnots,
                                                   spline_params_group2$Event$Coefficients)}
  
  PHF2.v <- function(t) {hazard_function_cloglog.v(t, spline_params_group2$Event$Knots,
                                                   spline_params_group2$Event$Degree, spline_params_group2$Event$BKnots,
                                                   spline_params_group2$Event$Coefficients)}
  PRF2.v <- function(t) {survival_function_cloglog.v(t, spline_params_group2$Risk$Knots,
                                                     spline_params_group2$Risk$Degree, spline_params_group2$Risk$BKnots,
                                                     spline_params_group2$Risk$Coefficients)}
  risk_integrand <- function(t) {
    return(PRF1.v(t)*PHF.v(t))
  }
  observed_integrand <- function(t){
    return(PRF1.v(t)*PHF1.v(t))
  }
  expected1 <- spline_params_group1$N*hybrid_integration(risk_integrand, 0, spline_params_group1$Max, disconts = NULL, pivot=restriction)
  observed1 <- spline_params_group1$N*hybrid_integration(observed_integrand, 0, spline_params_group1$Max, disconts = NULL, pivot=restriction)
  risk_integrand <- function(t) {
    return(PRF2.v(t)*PHF.v(t))
  }
  observed_integrand <- function(t){
    return(PRF2.v(t)*PHF2.v(t))
  }
  expected2 <- spline_params_group2$N*hybrid_integration(risk_integrand, 0, spline_params_group2$Max, disconts = NULL, pivot=restriction)
  observed2 <- spline_params_group2$N*hybrid_integration(observed_integrand, 0, spline_params_group2$Max, disconts = NULL, pivot=restriction)
  LR_STAT <- (observed1-expected1)^2/expected1 + (observed2-expected2)^2/expected2
  print(expected1)
  print(observed1)
  print(expected2)
  print(observed2)
  return(LR_STAT)
}

hazard_function_cloglog <- function(t, knots, degree, boundary_knots, coefficients) {
  final_knot <- knots[length(knots)]
  if (t < knots[1]) {
    S_T1 <- survival_function_cloglog(knots[1], knots, degree, boundary_knots, coefficients)
    lambda <- -log(S_T1)/knots[1]
    return(lambda)
  }
  else if (t > final_knot) {
    lambda <- hazard_function_cloglog(final_knot, knots, degree, boundary_knots, coefficients)
    return(lambda)
  }
  else {
    S_T <- survival_function_cloglog(t, knots, degree, boundary_knots, coefficients)
    dbasis <- cbind(rep(0, length(t)), mSpline(t, knots=knots, degree=degree, Boundary.knots = boundary_knots, intercept=TRUE, periodic=FALSE))
    basis <- cbind(rep(1, length(t)), iSpline(t, knots=knots, degree=degree, Boundary.knots = boundary_knots))
    term1 <- cloglog_inv_deriv(coefficients %*% t(basis))
    term2 <- coefficients %*% t(dbasis)
    haz <- -term1*term2/S_T
    haz <- ifelse(haz <= 0, 0, haz)
    return(haz)
  }
}

squared_sum_influence <- function(time, delta, spline_params, confint_time, restriction=0, weights=rep(1, length(time))) {
  PHF.v <- function(t) {hazard_function_cloglog.v(t, spline_params$Event$Knots,
                                                  spline_params$Event$Degree, spline_params$Event$BKnots,
                                                  spline_params$Event$Coefficients)}
  
  PSF.v <- function(t) {survival_function_cloglog.v(t, spline_params$Event$Knots,
                                                    spline_params$Event$Degree, spline_params$Event$BKnots,
                                                    spline_params$Event$Coefficients)}
  PRF.v <- function(t) {survival_function_cloglog.v(t, spline_params$Risk$Knots,
                                                    spline_params$Risk$Degree, spline_params$Risk$BKnots,
                                                    spline_params$Risk$Coefficients)}
  term1 <- delta*I(time <= confint_time) / PRF.v(time)
  time_trunc <- ifelse(time <= confint_time, time, confint_time)
  integrand <- function(u) return(PHF.v(u)/PRF.v(u))
  term2 <- fast_hybrid_integration(integrand, 0, time_trunc, pivot=restriction)
  const <- weights/log(PSF.v(confint_time))
  influence_vec <- const*(term1-term2)
  return(sum(influence_vec^2))
}

squared_sum_influence_logrank <- function(time, delta, treatment, spline_params, spline_params_treated, restriction=0, weights=rep(1, length(time)), p_treated=0.5) {
  PHF.v <- function(t) {hazard_function_cloglog.v(t, spline_params$Event$Knots,
                                                  spline_params$Event$Degree, spline_params$Event$BKnots,
                                                  spline_params$Event$Coefficients)}
  PRF.v <- function(t) {survival_function_cloglog.v(t, spline_params$Risk$Knots,
                                                    spline_params$Risk$Degree, spline_params$Risk$BKnots,
                                                    spline_params$Risk$Coefficients)}
  PRFT.v <- function(t) {survival_function_cloglog.v(t, spline_params_treated$Risk$Knots,
                                                    spline_params_treated$Risk$Degree, spline_params_treated$Risk$BKnots,
                                                    spline_params_treated$Risk$Coefficients)}
  term1 <- delta*(treatment - p_treated*PRFT.v(time)/PRF.v(time))
  integrand <- function(u) {
    haz <- PHF.v(u)
    return(p_treated*haz*PRFT.v(u)/PRF.v(u))}
  term2 <- fast_hybrid_integration(integrand, 0, time, pivot=restriction)
  integrand <- function(u) return(PHF.v(u))
  term3 <- fast_hybrid_integration(integrand, 0, time, pivot=restriction)
  influence_vec <- weights*(term1+term2-term3*treatment)
  return(sum((influence_vec)^2))
}

get_survival_splines <- function(data, time="time", event="delta", degree=2, knots=5, max_time=max(data[,time])) {
  
  n <- length(data[,time])
  data[,time] <- ifelse(data[,time] > max_time, max_time, data[,time])
  Event_Curve <- survfit(Surv(data[,time], data[,event]) ~ 1)
  Event_Data <- data.frame(Time = Event_Curve$time, S_T = Event_Curve$surv)
  Event_Data$S_T[length(Event_Data$Time)] = 0
  Risk_Set_Data <- data.frame(Time = Event_Curve$time, S_T = Event_Curve$n.risk/Event_Curve$n)
  t_q <- get_time_quantiles(Event_Data$Time, Event_Data$S_T, seq(1,0,-1/(knots+1))[2:(knots+1)])
  basis <- iSpline(Event_Data$Time, knots=t_q, degree=degree, Boundary.knots = c(0,max(Event_Data$Time)))
  Spline_Event <- glm(S_T ~ basis, family=quasibinomial(link="logit"), data=Event_Data)
  bknots <- c(0,max(Event_Data$Time))
  Event_Parameters <- list(t_q, degree, bknots, Spline_Event$coefficients)
  names(Event_Parameters) <- c("Knots", "Degree", "BKnots", "Coefficients")
  
  t_q_risk <- get_time_quantiles(Risk_Set_Data$Time, Risk_Set_Data$S_T, seq(1,0,-1/(knots+1))[2:(knots+1)])
  basis <- iSpline(Risk_Set_Data$Time, knots=t_q_risk, degree=degree, Boundary.knots = c(0,max(Risk_Set_Data$Time)))
  bknots_risk <- c(0,max(Risk_Set_Data$Time))
  Spline_Risk <- glm(S_T ~ basis, family=quasibinomial(link="logit"), data=Risk_Set_Data)
  Risk_Parameters <- list(t_q_risk, degree, bknots_risk, Spline_Risk$coefficients)
  names(Risk_Parameters) <- c("Knots", "Degree", "BKnots", "Coefficients")
  
  final_output <- list(Event_Parameters, Risk_Parameters, n, max_time)
  names(final_output) <- c("Event", "Risk", "N", "Max")
  return(final_output)
}

get_survival_splines_cloglog <- function(data, time="time", event="delta", degree=2, knots=5, max_time=max(data[,time]), bknots=c(0, max_time), weights=rep(1,nrow(data)),
                                         confint_times=NULL, confint_restriction=0) {
  
  n <- sum(weights)
  data[,time] <- ifelse(data[,time] > max_time, max_time, data[,time])
  Event_Curve <- survfit(Surv(data[,time], data[,event]) ~ 1, weights=weights)
  Event_Data <- data.frame(Time = Event_Curve$time, S_T = Event_Curve$surv)
  Event_Data <- filter(Event_Data, S_T != 1, Time > bknots[1], Time < bknots[2])
  max_ST <- max(Event_Data$S_T)
  min_ST <- min(Event_Data$S_T)
  Risk_Curve <- survfit(Surv(data[,time], rep(1,nrow(data))) ~ 1, weights=weights)
  Risk_Set_Data <- data.frame(Time = Risk_Curve$time, S_T = Risk_Curve$surv)
  Risk_Set_Data <- filter(Risk_Set_Data, S_T != 1, Time > bknots[1], Time < bknots[2])
  t_q <- get_time_quantiles(Event_Data$Time, Event_Data$S_T, seq(max_ST,min_ST,(-max_ST+min_ST)/(knots+1))[2:(knots+1)])

  basis <- iSpline(Event_Data$Time, knots=t_q, degree=degree, Boundary.knots = bknots)
  Spline_Event <- glm(S_T ~ basis, family=quasibinomial(link="cloglog"), data=Event_Data)
  Event_Parameters <- list(t_q, degree, bknots, Spline_Event$coefficients)
  names(Event_Parameters) <- c("Knots", "Degree", "BKnots", "Coefficients")
  min_YT <- min(Risk_Set_Data$S_T)
  max_YT <- max(Risk_Set_Data$S_T)
  

  t_q_risk <- get_time_quantiles(Risk_Set_Data$Time, Risk_Set_Data$S_T, seq(max_YT,min_YT,(-max_YT+min_YT)/(knots+1))[2:(knots+1)])
  basis <- iSpline(Risk_Set_Data$Time, knots=t_q_risk, degree=degree, Boundary.knots = bknots)
  Spline_Risk <- glm(S_T ~ basis, family=quasibinomial(link="cloglog"), data=Risk_Set_Data)
  Risk_Parameters <- list(t_q_risk, degree, bknots, Spline_Risk$coefficients)
  names(Risk_Parameters) <- c("Knots", "Degree", "BKnots", "Coefficients")
  final_output <- list(Event_Parameters, Risk_Parameters, n, max_time)
  names(final_output) <- c("Event", "Risk", "N", "Max")
  influence_sums <- list()
  for (i in confint_times) {
    influence_sums[as.character(i)] <- squared_sum_influence(data[,time], data[,event], final_output, i, confint_restriction, weights)
  }
  final_output <- list(Event_Parameters, Risk_Parameters, n, max_time, influence_sums)
  names(final_output) <- c("Event", "Risk", "N", "Max", "Influence")
  return(final_output)
}


theoretical_KM_PS <- function(spline_params, t_ps, time, delta, restriction=0) {
  PSF.v <- function(t) {survival_function_cloglog.v(t, spline_params$Event$Knots,
                                                            spline_params$Event$Degree, spline_params$Event$BKnots,
                                                            spline_params$Event$Coefficients)}
  PRF.v <- function(t) {survival_function_cloglog.v(t, spline_params$Risk$Knots,
                                                            spline_params$Risk$Degree, spline_params$Risk$BKnots,
                                                            spline_params$Risk$Coefficients)}
  PHF.v <- function(t) {hazard_function_cloglog.v(t, spline_params$Event$Knots,
                                                         spline_params$Event$Degree, spline_params$Event$BKnots,
                                                         spline_params$Event$Coefficients)}
  S_T <- PSF.v(t_ps)
  EY_X <- PRF.v(time)
  term1 <- as.numeric(delta*I(time <= t_ps) / EY_X)
  upper_lims <- ifelse(t_ps < time, t_ps, time)
  lims_data <- data.frame(ID = seq(1, length(upper_lims)), upper_lims)
  lims_data <- lims_data %>% arrange(upper_lims)
  integrand <- function(t) {
    hazard <- PHF.v(t)
    EY_T <- PRF.v(t)
    return(hazard/EY_T)}
  term2 <- hybrid_integration(integrand, 0, lims_data$upper_lims, disconts=NULL, pivot=restriction)
  lims_data$term2 <- term2
  lims_data <- lims_data %>% arrange(ID)
  term2 <- lims_data$term2
  return(-c(S_T)*(term1 - term2) + c(S_T))
}

update_survival_splines <- function(spline_params, time, delta,
                                    breakpoints=5, knots = length(spline_params$Event$Knots),
                                    degree = spline_params$Event$Degree, max_time=spline_params$Max, restriction=0) {
  time <- ifelse(time>max_time, max_time, time)
  n_to_add <- length(time)
  
  PSF.v <- function(t) {survival_function_cloglog.v(t, spline_params$Event$Knots,
                                                    spline_params$Event$Degree, spline_params$Event$BKnots,
                                                    spline_params$Event$Coefficients)}
  PRF.v <- function(t) {survival_function_cloglog.v(t, spline_params$Risk$Knots,
                                                    spline_params$Risk$Degree, spline_params$Risk$BKnots,
                                                    spline_params$Risk$Coefficients)}
  PHF.v <- function(t) {hazard_function_cloglog.v(t, spline_params$Event$Knots,
                                                           spline_params$Event$Degree, spline_params$Event$BKnots,
                                                           spline_params$Event$Coefficients)}
  PRHF.v <- function(t) {hazard_function_cloglog.v(t, spline_params$Risk$Knots,
                                                              spline_params$Risk$Degree, spline_params$Risk$BKnots,
                                                              spline_params$Risk$Coefficients)}
  # FIRST GET SPLINE FOR SURVIVAL FUNCTION
  
  t_q <- NULL
  all_knots <- c(spline_params$Event$BKnots[1], spline_params$Event$Knots, spline_params$Event$BKnots[2])
  for (i in seq(1,length(all_knots) - 1)){
    inc <-  (all_knots[i+1] - all_knots[i]) / (breakpoints + 1)
    t_q <- c(t_q, seq(all_knots[i] + inc, all_knots[i+1] - inc, inc))
  }
  current_values <- PSF.v(t_q)
  event_part <- NULL
  risk_t <- PRF.v(time)
  for (i in t_q) {
    delta_t <- delta*I(time <= i)
    event_part <- c(event_part, sum(delta_t/risk_t))
  }
  risk_set.v <- function(t) {
    return(colSums(outer(time, t, ">")))
  }
  integrand <- function(t) {
    hazard <- PHF.v(t)
    EY_T <- PRF.v(t)
    risk_t_new <- risk_set.v(t)
    return(hazard*risk_t_new/EY_T)
  }
  risk_part <- hybrid_integration(integrand, 0, t_q, disconts=c(unique(time)), pivot=restriction)
  divisor <- 0
  for (i in c(1:n_to_add)) {divisor <- divisor + 1/(i+spline_params$N)}
  divisor <- divisor / n_to_add
  new_values <- current_values - (current_values*divisor)*(event_part-risk_part)
  new_values <- ifelse(new_values > 1, 1, new_values)
  new_values <- ifelse(new_values < 0, 0, new_values)
  # need to transpose values when I don't have const hazard constraints on edges
  adjusted_data <- data.frame(Time = t_q, S_T = new_values)
  if (knots == length(spline_params$Event$Knots)) {t_knots <- spline_params$Event$Knots}
  else {
    full_prev <- c(spline_params$Event$BKnots[1], spline_params$Event$Knots, spline_params$Event$BKnots[2])
    inc <- (length(full_prev) - 1) / length(full_prev)
    placements <- seq(1+inc, length(full_prev)-inc, inc)
    t_knots <- NULL
    for (i in placements) {
      new_t <- full_prev[floor(i)]*(ceiling(i)-i) + full_prev[ceiling(i)]*(i-floor(i)) 
      t_knots <- c(t_knots, new_t)
    }
  }
  basis <- iSpline(adjusted_data$Time, knots=t_knots, degree=degree, Boundary.knots = spline_params$Event$BKnots)
  Spline_Event <- glm(S_T ~ basis, family=quasibinomial(link="cloglog"), data=adjusted_data)
  bknots <- spline_params$Event$BKnots
  Event_Parameters <- list(t_knots, degree, bknots, Spline_Event$coefficients)
  names(Event_Parameters) <- c("Knots", "Degree", "BKnots", "Coefficients")
  
  # THEN GET SPLINES FOR RISK FUNCTION
  t_q <- NULL
  all_knots <- c(spline_params$Risk$BKnots[1], spline_params$Risk$Knots, spline_params$Risk$BKnots[2])
  for (i in seq(1,length(all_knots) - 1)){
    inc <-  (all_knots[i+1] - all_knots[i]) / (breakpoints + 1)
    t_q <- c(t_q, seq(all_knots[i] + inc, all_knots[i+1] - inc, inc))
  }
  current_values <- PRF.v(t_q)
  event_part <- NULL
  risk_t <- PRF.v(time)
  for (i in t_q) {
    delta_t <- I(time <= i)
    event_part <- c(event_part, sum(delta_t/risk_t))
  }
  integrand <- function(t) {
    hazard <- PRHF.v(t)
    EY_T <- PRF.v(t)
    risk_t_new <- risk_set.v(t)
    return(hazard*risk_t_new/EY_T)
  }
  risk_part <- hybrid_integration(integrand, 0, t_q, disconts=c(unique(time)), pivot=restriction)
  new_values_risk <- current_values - (current_values*divisor)*(event_part-risk_part)
  new_values <- ifelse(new_values_risk > 1, 1, new_values_risk)
  new_values_risk <- ifelse(new_values_risk < 0, 0, new_values_risk)
  adjusted_data <- data.frame(Time = t_q, Y_T = new_values_risk)
  
  if (knots == length(spline_params$Risk$Knots)) {t_knots <- spline_params$Risk$Knots}
  else {
    full_prev <- c(spline_params$Risk$BKnots[1], spline_params$Risk$Knots, spline_params$Risk$BKnots[2])
    inc <- (length(full_prev) - 1) / length(full_prev)
    placements <- seq(1+inc, length(full_prev)-inc, inc)
    t_knots <- NULL
    for (i in placements) {
      new_t <- full_prev[floor(i)]*(ceiling(i)-i) + full_prev[ceiling(i)]*(i-floor(i)) 
      t_knots <- c(t_knots, new_t)
      }
  }
  basis <- iSpline(adjusted_data$Time, knots=t_knots, degree=degree, Boundary.knots = spline_params$Risk$BKnots)
  adjusted_data$basis <- basis
  Spline_Risk <- glm(Y_T ~ basis, family=quasibinomial(link="cloglog"), data=adjusted_data)
  bknots <- spline_params$Risk$BKnots
  Risk_Parameters <- list(t_knots, degree, bknots, Spline_Risk$coefficients)
  names(Risk_Parameters) <- c("Knots", "Degree", "BKnots", "Coefficients")
  n <- length(time) + spline_params$N
  final_output <- list(Event_Parameters, Risk_Parameters, n, max_time)
  names(final_output) <- c("Event", "Risk", "N", "Max")
  return(final_output)
}


update_survival_splines_weighted <- function(spline_params, time, delta, weights=rep(1, length(time)),
                                    breakpoints=5, knots = length(spline_params$Event$Knots),
                                    degree = spline_params$Event$Degree, confint_times=names(spline_params$Influence), max_time=spline_params$Max, restriction=0) {
  time <- ifelse(time>max_time, max_time, time)
  n_to_add <- length(time)
  
  PSF.v <- function(t) {survival_function_cloglog.v(t, spline_params$Event$Knots,
                                                    spline_params$Event$Degree, spline_params$Event$BKnots,
                                                    spline_params$Event$Coefficients)}
  PRF.v <- function(t) {survival_function_cloglog.v(t, spline_params$Risk$Knots,
                                                    spline_params$Risk$Degree, spline_params$Risk$BKnots,
                                                    spline_params$Risk$Coefficients)}
  PHF.v <- function(t) {hazard_function_cloglog.v(t, spline_params$Event$Knots,
                                                  spline_params$Event$Degree, spline_params$Event$BKnots,
                                                  spline_params$Event$Coefficients)}
  PRHF.v <- function(t) {hazard_function_cloglog.v(t, spline_params$Risk$Knots,
                                                   spline_params$Risk$Degree, spline_params$Risk$BKnots,
                                                   spline_params$Risk$Coefficients)}
  # FIRST GET SPLINE FOR SURVIVAL FUNCTION
  t_q <- NULL
  all_knots <- c(spline_params$Event$BKnots[1], spline_params$Event$Knots, spline_params$Event$BKnots[2])
  for (i in seq(1,length(all_knots) - 1)){
    inc <-  (all_knots[i+1] - all_knots[i]) / (breakpoints + 1)
    t_q <- c(t_q, seq(all_knots[i] + inc, all_knots[i+1] - inc, inc))
  }
  current_values <- PSF.v(t_q)
  event_part <- NULL
  risk_t <- PRF.v(time)
  for (i in t_q) {
    delta_t <- weights*delta*I(time <= i)
    event_part <- c(event_part, sum(delta_t/risk_t))
  }
  risk_set.v <- function(t) {
    return(colSums(weights %*% outer(time, t, ">")))
  }
  integrand <- function(t) {
    hazard <- PHF.v(t)
    EY_T <- PRF.v(t)
    risk_t_new <- risk_set.v(t)
    return(hazard*risk_t_new/EY_T)
  }
  risk_part <- hybrid_integration(integrand, 0, t_q, disconts=c(unique(time)), pivot=restriction)
  divisor <- 0
  for (i in c(1:n_to_add)) {divisor <- divisor + 1/(sum(weights[1:i])+spline_params$N)}
  divisor <- divisor / n_to_add
  new_values <- current_values - (current_values*divisor)*(event_part-risk_part)
  new_values <- ifelse(new_values > 1, 1, new_values)
  new_values <- ifelse(new_values < 0, 0, new_values)
  # need to transpose values when I don't have const hazard constraints on edges
  adjusted_data <- data.frame(Time = t_q, S_T = new_values)
  if (knots == length(spline_params$Event$Knots)) {t_knots <- spline_params$Event$Knots}
  else {
    full_prev <- c(spline_params$Event$BKnots[1], spline_params$Event$Knots, spline_params$Event$BKnots[2])
    inc <- (length(full_prev) - 1) / length(full_prev)
    placements <- seq(1+inc, length(full_prev)-inc, inc)
    t_knots <- NULL
    for (i in placements) {
      new_t <- full_prev[floor(i)]*(ceiling(i)-i) + full_prev[ceiling(i)]*(i-floor(i)) 
      t_knots <- c(t_knots, new_t)
    }
  }
  basis <- iSpline(adjusted_data$Time, knots=t_knots, degree=degree, Boundary.knots = spline_params$Event$BKnots)
  Spline_Event <- glm(S_T ~ basis, family=quasibinomial(link="cloglog"), data=adjusted_data)
  bknots <- spline_params$Event$BKnots
  Event_Parameters <- list(t_knots, degree, bknots, Spline_Event$coefficients)
  names(Event_Parameters) <- c("Knots", "Degree", "BKnots", "Coefficients")
  
  # THEN GET SPLINES FOR RISK FUNCTION
  t_q <- NULL
  all_knots <- c(spline_params$Risk$BKnots[1], spline_params$Risk$Knots, spline_params$Risk$BKnots[2])
  for (i in seq(1,length(all_knots) - 1)){
    inc <-  (all_knots[i+1] - all_knots[i]) / (breakpoints + 1)
    t_q <- c(t_q, seq(all_knots[i] + inc, all_knots[i+1] - inc, inc))
  }
  current_values <- PRF.v(t_q)
  event_part <- NULL
  risk_t <- PRF.v(time)
  for (i in t_q) {
    delta_t <- weights*I(time <= i)
    event_part <- c(event_part, sum(delta_t/risk_t))
  }
  integrand <- function(t) {
    hazard <- PRHF.v(t)
    EY_T <- PRF.v(t)
    risk_t_new <- risk_set.v(t)
    return(hazard*risk_t_new/EY_T)
  }
  risk_part <- hybrid_integration(integrand, 0, t_q, disconts=c(unique(time)), pivot=restriction)
  new_values_risk <- current_values - (current_values*divisor)*(event_part-risk_part)
  new_values <- ifelse(new_values_risk > 1, 1, new_values_risk)
  new_values_risk <- ifelse(new_values_risk < 0, 0, new_values_risk)
  adjusted_data <- data.frame(Time = t_q, Y_T = new_values_risk)
  if (knots == length(spline_params$Risk$Knots)) {t_knots <- spline_params$Risk$Knots}
  else {
    full_prev <- c(spline_params$Risk$BKnots[1], spline_params$Risk$Knots, spline_params$Risk$BKnots[2])
    inc <- (length(full_prev) - 1) / length(full_prev)
    placements <- seq(1+inc, length(full_prev)-inc, inc)
    t_knots <- NULL
    for (i in placements) {
      new_t <- full_prev[floor(i)]*(ceiling(i)-i) + full_prev[ceiling(i)]*(i-floor(i)) 
      t_knots <- c(t_knots, new_t)
    }
  }
  basis <- iSpline(adjusted_data$Time, knots=t_knots, degree=degree, Boundary.knots = spline_params$Risk$BKnots)
  adjusted_data$basis <- basis
  Spline_Risk <- glm(Y_T ~ basis, family=quasibinomial(link="cloglog"), data=adjusted_data)
  bknots <- spline_params$Risk$BKnots
  Risk_Parameters <- list(t_knots, degree, bknots, Spline_Risk$coefficients)
  names(Risk_Parameters) <- c("Knots", "Degree", "BKnots", "Coefficients")
  n <- sum(weights) + spline_params$N
  influence_sums <- spline_params$Influence
  for (i in confint_times) {
    influence_sums[as.character(i)] <- as.numeric(influence_sums[as.character(i)]) + squared_sum_influence(time,delta, spline_params, i, restriction, weights)
  }
  final_output <- list(Event_Parameters, Risk_Parameters, n, max_time, influence_sums)
  names(final_output) <- c("Event", "Risk", "N", "Max", "Influence")
  return(final_output)
}

update_survival_splines_chunk <- function(spline_params, time, delta, chunksize,
breakpoints=5, knots_list = rep(length(spline_params$Event$Knots), ceiling(length(time)/chunksize)),
degree = spline_params$Event$Degree, max_time=spline_params$Max, loud=TRUE, restriction=0) {
  updated_splines <- spline_params
  j <- 1
  for (i in seq(1, length(time), chunksize)) {
    if (loud) {
    print(i)
    print(i+chunksize-1)}
    if (i+chunksize < length(time)) {
      chunk_time <- time[c(i:(i+chunksize-1))]
      chunk_delta <- delta[c(i:(i+chunksize-1))]
    }
    else{
      chunk_time <- time[c(i:length(time))]
      chunk_delta <- delta[c(i:length(time))]
    }
    updated_splines <- update_survival_splines(updated_splines, chunk_time, chunk_delta,
                                               breakpoints=breakpoints, knots = knots_list[j],
                                               degree = spline_params$Event$Degree, max_time=spline_params$Max, restriction=restriction)
    j <- j + 1
  }
  return(updated_splines)
}


update_survival_splines_chunk_weighted <- function(spline_params, time, delta, chunksize, weights=rep(1, length(time)),
                                          breakpoints=5, knots_list = rep(length(spline_params$Event$Knots), ceiling(length(time)/chunksize)),
                                          degree = spline_params$Event$Degree, confint_times=names(spline_params$Influence), max_time=spline_params$Max, loud=TRUE, restriction=0) {
  updated_splines <- spline_params
  j <- 1
  for (i in seq(1, length(time)-1, chunksize)) {
    if (i+chunksize < length(time)) {
      if (loud) {
        print(i)
        print(i+chunksize-1)}
      chunk_time <- time[c(i:(i+chunksize-1))]
      chunk_delta <- delta[c(i:(i+chunksize-1))]
      chunk_weights <- weights[c(i:(i+chunksize-1))]
    }
    else{
      if (loud) {
        print(i)
        print(length(time))}
      chunk_time <- time[c(i:length(time))]
      chunk_delta <- delta[c(i:length(time))]
      chunk_weights <- weights[c(i:length(time))]
    }
    updated_splines <- update_survival_splines_weighted(updated_splines, chunk_time, chunk_delta,
                                               breakpoints=breakpoints, weights=chunk_weights, knots = knots_list[j],
                                               degree = updated_splines$Event$Degree, confint_times = confint_times, max_time=updated_splines$Max, restriction=restriction)
    j <- j + 1
  }
  return(updated_splines)
}

