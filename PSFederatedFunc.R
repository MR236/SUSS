library(survival)
library(tidyverse)
library(splines)
library(splines2)
library(intccr)
library(pseudo)
library(survminer)
library(rmutil)


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

survival_function_cloglog.v <- function(t, knots, degree, boundary_knots, coefficients) {
  final_knot <- knots[length(knots)]
  first_knot <- knots[1]
  basis_T1 <- c(1, iSpline(first_knot, knots=knots, degree=degree, Boundary.knots=boundary_knots))
  S_T1 <- cloglog_inv(coefficients %*% basis_T1)
  lambda_T1 <- -log(S_T1) / knots[1]
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
  final_est <- ifelse(t < first_knot, est_1, ifelse(t > final_knot, est_2, est_3))
  return(final_est)
}

hazard_function_cloglog.v <- function(t, knots, degree, boundary_knots, coefficients) {
  final_knot <- knots[length(knots)]
  first_knot <- knots[1]
  basis_T1 <- c(1, iSpline(first_knot, knots=knots, degree=degree, Boundary.knots=boundary_knots))
  S_T1 <- cloglog_inv(coefficients %*% basis_T1)
  lambda_T1 <- -log(S_T1) / knots[1]
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
  final_haz <- ifelse(t < first_knot, lambda_T1, ifelse(t > final_knot, haz_TF, haz))
  return(final_haz)
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

get_survival_splines_cloglog <- function(data, time="time", event="delta", degree=2, knots=5, max_time=max(data[,time])) {
  
  n <- length(data[,time])
  data[,time] <- ifelse(data[,time] > max_time, max_time, data[,time])
  data[,event] <- ifelse(data[,time] == max_time, 1, data[,event])
  Event_Curve <- survfit(Surv(data[,time], data[,event]) ~ 1)
  Event_Data <- data.frame(Time = Event_Curve$time, S_T = Event_Curve$surv)
  Event_Data$S_T[length(Event_Data$Time)] = 0
  first_ob <- data.frame(Time = 0, S_T = 1)
  Event_Data <- filter(Event_Data, S_T != 1)
  Event_Data <- rbind(first_ob, Event_Data) 
  Risk_Set_Data <- data.frame(Time = Event_Curve$time, S_T = Event_Curve$n.risk/Event_Curve$n)
  Risk_Set_Data <- filter(Risk_Set_Data, S_T != 1)
  Risk_Set_Data <- rbind(first_ob, Risk_Set_Data) 
  t_q <- get_time_quantiles(Event_Data$Time, Event_Data$S_T, seq(1,0,-1/(knots+1))[2:(knots+1)])
  basis <- iSpline(Event_Data$Time, knots=t_q, degree=degree, Boundary.knots = c(0,max(Event_Data$Time)))
  Spline_Event <- glm(S_T ~ basis, family=quasibinomial(link="cloglog"), data=Event_Data)
  bknots <- c(0,max(Event_Data$Time))
  Event_Parameters <- list(t_q, degree, bknots, Spline_Event$coefficients)
  names(Event_Parameters) <- c("Knots", "Degree", "BKnots", "Coefficients")
  
  t_q_risk <- get_time_quantiles(Risk_Set_Data$Time, Risk_Set_Data$S_T, seq(1,0,-1/(knots+1))[2:(knots+1)])
  basis <- iSpline(Risk_Set_Data$Time, knots=t_q_risk, degree=degree, Boundary.knots = c(0,max(Risk_Set_Data$Time)))
  bknots_risk <- c(0,max(Risk_Set_Data$Time))
  Spline_Risk <- glm(S_T ~ basis, family=quasibinomial(link="cloglog"), data=Risk_Set_Data)
  Risk_Parameters <- list(t_q_risk, degree, bknots_risk, Spline_Risk$coefficients)
  names(Risk_Parameters) <- c("Knots", "Degree", "BKnots", "Coefficients")
  
  final_output <- list(Event_Parameters, Risk_Parameters, n, max_time)
  names(final_output) <- c("Event", "Risk", "N", "Max")
  return(final_output)
}

theoretical_KM_PS <- function(spline_params, t_ps, time, delta) {
  # Prior_Surv_Func <- function(t) {survival_function_cloglog(t, spline_params$Event$Knots,
  #                                                           spline_params$Event$Degree, spline_params$Event$BKnots,
  #                                                           spline_params$Event$Coefficients)}
  # Prior_Risk_Func <- function(t) {survival_function_cloglog(t, spline_params$Risk$Knots,
  #                                                           spline_params$Risk$Degree, spline_params$Risk$BKnots,
  #                                                           spline_params$Risk$Coefficients)}
  # Prior_Haz_Func <- function(t) {hazard_function_cloglog(t, spline_params$Event$Knots,
  #                                                        spline_params$Event$Degree, spline_params$Event$BKnots,
  #                                                        spline_params$Event$Coefficients)}
  # PSF.v <- Vectorize(Prior_Surv_Func)
  # PRF.v <- Vectorize(Prior_Risk_Func)
  # PHF.v <- Vectorize(Prior_Haz_Func)
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
  integrand <- function(t) {
    hazard <- PHF.v(t)
    EY_T <- PRF.v(t)
    return(hazard/EY_T)
  }
  integrate_time <- function(t) {return(integrate(integrand, 0, min(t_ps, t))$value)}
  v.integrate_time <- Vectorize(integrate_time)
  term2 <- v.integrate_time(time)
  return(-c(S_T)*(term1 - term2) + c(S_T))
}

update_survival_splines <- function(spline_params, time, delta,
                                    breakpoints=100, knots = length(spline_params$Event$Knots),
                                    degree = spline_params$Event$Degree, max_time=spline_params$Max) {
  time <- ifelse(time>max_time, max_time, time)
  delta <- ifelse(time==max_time, 1, delta)
  n_to_add <- length(time)
  # Prior_Surv_Func <- function(t) {survival_function_cloglog(t, spline_params$Event$Knots,
  #                                                   spline_params$Event$Degree, spline_params$Event$BKnots,
  #                                                   spline_params$Event$Coefficients)}
  # Prior_Risk_Func <- function(t) {survival_function_cloglog(t, spline_params$Risk$Knots,
  #                                                   spline_params$Risk$Degree, spline_params$Risk$BKnots,
  #                                                   spline_params$Risk$Coefficients)}
  # Prior_Haz_Func <- function(t) {hazard_function_cloglog(t, spline_params$Event$Knots,
  #                                                          spline_params$Event$Degree, spline_params$Event$BKnots,
  #                                                          spline_params$Event$Coefficients)}
  # Prior_Risk_Haz_Func <- function(t) {hazard_function_cloglog(t, spline_params$Risk$Knots,
  #                                                             spline_params$Risk$Degree, spline_params$Risk$BKnots,
  #                                                             spline_params$Risk$Coefficients)}
  # PSF.v <- Vectorize(Prior_Surv_Func)
  # PRF.v <- Vectorize(Prior_Risk_Func)
  # PHF.v <- Vectorize(Prior_Haz_Func)
  # PRHF.v <- Vectorize(Prior_Risk_Haz_Func)
  
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
  
  # eventually want equally spaced quantiles
  #t_q <- NULL
  #for (i in s_q) {t_q <- c(t_q, numeric_inverse(Prior_Surv_Func, i, upper=upper_lim))}
  inc <- (spline_params$Risk$BKnots[2] - spline_params$Risk$BKnots[1]) / (breakpoints + 1)
  t_q <- seq(spline_params$Risk$BKnots[1] + inc, spline_params$Risk$BKnots[2] - inc, inc)
  current_values <- PSF.v(t_q)
  event_part <- NULL
  risk_t <- PRF.v(time)
  for (i in t_q) {
    delta_t <- delta*I(time <= i)
    event_part <- c(event_part, sum(delta_t/risk_t))
  }
  # risk_set <- function(t){return(sum(I(time>t)))}
  # risk_set.v <- Vectorize(risk_set)
  risk_set.v <- function(t) {
    return(colSums(outer(time, t, ">")))
  }
  integrand <- function(t) {
    hazard <- PHF.v(t)
    EY_T <- PRF.v(t)
    risk_t_new <- risk_set.v(t)
    return(hazard*risk_t_new/EY_T)
  }
  # integrate_time <- function(t) {return(integrate(integrand, 0, t, rel.tol=0.1)$value)}
  # v.integrate_time <- Vectorize(integrate_time)
  v.integrate_time <- function(t) {return(int(integrand, 0, t))}
  risk_part <- v.integrate_time(t_q)
  divisor <- 0
  for (i in c(1:n_to_add)) {divisor <- divisor + 1/(i+spline_params$N)}
  divisor <- divisor / n_to_add
  new_values <- current_values - (current_values*divisor)*(event_part-risk_part)
  new_values <- ifelse(new_values > 1, 1, new_values)
  new_values <- ifelse(new_values < 0, 0, new_values)
  adjusted_data <- data.frame(Time = t_q, S_T = new_values)
  inc_knots <- 1 / (knots + 1)
  knots_cut <- seq(1-inc_knots, inc_knots, -inc_knots)
  indices <- NULL
  for (i in knots_cut) {
    indices <- c(indices, min(which(adjusted_data$S_T < i)))
  }
  t_knots <- adjusted_data$Time[indices]
  # again, eventually want knots based on quantiles like in the first iteration
  #inc_knots <- (spline_params$Event$BKnots[2] - spline_params$Event$BKnots[1]) / (knots + 1)
  #t_knots <- seq(spline_params$Event$BKnots[1] + inc_knots, spline_params$Event$BKnots[2] - inc_knots, inc_knots)
  basis <- iSpline(adjusted_data$Time, knots=t_knots, degree=degree, Boundary.knots = spline_params$Event$BKnots)
  Spline_Event <- glm(S_T ~ basis, family=quasibinomial(link="cloglog"), data=adjusted_data)
  bknots <- spline_params$Event$BKnots
  Event_Parameters <- list(t_knots, degree, bknots, Spline_Event$coefficients)
  names(Event_Parameters) <- c("Knots", "Degree", "BKnots", "Coefficients")
  
  # THEN GET SPLINES FOR RISK FUNCTION
  #t_q <- NULL
  #for (i in s_q) {t_q <- c(t_q, numeric_inverse(Prior_Risk_Func, i, upper=upper_lim))}
  current_values <- PRF.v(t_q)
  event_part <- NULL
  risk_t <- PRF.v(time)
  for (i in t_q) {
    delta_t <- I(time <= i)
    event_part <- c(event_part, sum(delta_t/risk_t))
  }
  risk_set <- function(t){return(sum(I(time>t)))}
  risk_set.v <- Vectorize(risk_set)
  integrand <- function(t) {
    hazard <- PRHF.v(t)
    EY_T <- PRF.v(t)
    risk_t_new <- risk_set.v(t)
    return(hazard*risk_t_new/EY_T)
  }
  integrate_time <- function(t) {return(integrate(integrand, 0, t, rel.tol=0.1)$value)}
  
  v.integrate_time <- Vectorize(integrate_time)
  risk_part <- v.integrate_time(t_q)
  new_values_risk <- current_values - (current_values*divisor)*(event_part-risk_part)
  new_values <- ifelse(new_values_risk > 1, 1, new_values_risk)
  new_values_risk <- ifelse(new_values_risk < 0, 0, new_values_risk)
  adjusted_data <- data.frame(Time = t_q, Y_T = new_values_risk)
  #inc_knots <- (spline_params$Risk$BKnots[2] - spline_params$Risk$BKnots[1]) / (knots + 1)
  #t_knots <- seq(spline_params$Risk$BKnots[1] + inc_knots, spline_params$Risk$BKnots[2] - inc_knots, inc_knots)
  inc_knots <- 1 / (knots + 1)
  knots_cut <- knots_cut <- seq(1-inc_knots, inc_knots, -inc_knots)
  indices <- NULL
  for (i in knots_cut) {
    indices <- c(indices, min(which(adjusted_data$Y_T < i)))
  }
  t_knots <- adjusted_data$Time[indices]
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



update_survival_splines_chunk <- function(spline_params, time, delta, chunksize,
breakpoints=100, knots_list = rep(length(spline_params$Event$Knots), ceiling(length(time)/chunksize)),
degree = spline_params$Event$Degree, max_time=spline_params$Max) {
  updated_splines <- spline_params
  j <- 1
  for (i in seq(1, length(time), chunksize)) {
    print(i)
    print(i+chunksize-1)
    if (i+chunksize < length(time)) {
      chunk_time <- time[c(i:(i+chunksize-1))]
      chunk_delta <- delta[c(i:(i+chunksize-1))]
    }
    else{
      chunk_time <- time[c(i:length(time))]
      chunk_delta <- delta[c(i:length(time))]
    }
    updated_splines <- update_survival_splines(updated_splines, chunk_time, chunk_delta,
                                               breakpoints=100, knots = knots_list[j],
                                               degree = spline_params$Event$Degree, max_time=spline_params$Max)
    j <- j + 1
  }
  return(updated_splines)
}
