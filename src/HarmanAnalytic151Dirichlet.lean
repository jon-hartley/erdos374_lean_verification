import Erdos374_Update152

/- Current-object Harman dependency closure contracts and recursive axiom audit. -/
#print Erdos374.HarmanAnalytic151MeanSquare.exponentialKernel151
#print Erdos374.HarmanAnalytic151MeanSquare.exponentialSum151
#check Erdos374.HarmanAnalytic151MeanSquare.continuous_kernel151
#check Erdos374.HarmanAnalytic151MeanSquare.norm_kernel151
#check Erdos374.HarmanAnalytic151MeanSquare.kernel_zero151
#check Erdos374.HarmanAnalytic151MeanSquare.kernel_mul_conj151
#check Erdos374.HarmanAnalytic151MeanSquare.integral_kernel151
#check Erdos374.HarmanAnalytic151MeanSquare.norm_integral_kernel_le151
#check Erdos374.HarmanAnalytic151MeanSquare.continuous_sum151
#check Erdos374.HarmanAnalytic151MeanSquare.norm_square_expansion151
#check Erdos374.HarmanAnalytic151MeanSquare.mean_square_expansion151
#check Erdos374.HarmanAnalytic151MeanSquare.mean_square_diagonal151
#check Erdos374.HarmanAnalytic151MeanSquare.mean_square_error_le151
#check Erdos374.HarmanAnalytic151MeanSquare.log_difference_lower151
#check Erdos374.HarmanAnalytic151MeanSquare.inverse_log_difference_le151
#check Erdos374.HarmanAnalytic151MeanSquare.inverse_distance_row151
#check Erdos374.HarmanAnalytic151MeanSquare.inverse_log_row151
#check Erdos374.HarmanAnalytic151MeanSquare.quadratic_pair_bound151
#check Erdos374.HarmanAnalytic151MeanSquare.dirichlet_mean_square_error151
#check Erdos374.HarmanAnalytic151MeanSquare.dirichlet_mean_square_le151
#print axioms Erdos374.HarmanAnalytic151MeanSquare.exponentialKernel151
#print axioms Erdos374.HarmanAnalytic151MeanSquare.exponentialSum151
#print axioms Erdos374.HarmanAnalytic151MeanSquare.continuous_kernel151
#print axioms Erdos374.HarmanAnalytic151MeanSquare.norm_kernel151
#print axioms Erdos374.HarmanAnalytic151MeanSquare.kernel_zero151
#print axioms Erdos374.HarmanAnalytic151MeanSquare.kernel_mul_conj151
#print axioms Erdos374.HarmanAnalytic151MeanSquare.integral_kernel151
#print axioms Erdos374.HarmanAnalytic151MeanSquare.norm_integral_kernel_le151
#print axioms Erdos374.HarmanAnalytic151MeanSquare.continuous_sum151
#print axioms Erdos374.HarmanAnalytic151MeanSquare.norm_square_expansion151
#print axioms Erdos374.HarmanAnalytic151MeanSquare.mean_square_expansion151
#print axioms Erdos374.HarmanAnalytic151MeanSquare.mean_square_diagonal151
#print axioms Erdos374.HarmanAnalytic151MeanSquare.mean_square_error_le151
#print axioms Erdos374.HarmanAnalytic151MeanSquare.log_difference_lower151
#print axioms Erdos374.HarmanAnalytic151MeanSquare.inverse_log_difference_le151
#print axioms Erdos374.HarmanAnalytic151MeanSquare.inverse_distance_row151
#print axioms Erdos374.HarmanAnalytic151MeanSquare.inverse_log_row151
#print axioms Erdos374.HarmanAnalytic151MeanSquare.quadratic_pair_bound151
#print axioms Erdos374.HarmanAnalytic151MeanSquare.dirichlet_mean_square_error151
#print axioms Erdos374.HarmanAnalytic151MeanSquare.dirichlet_mean_square_le151

run_cmd do
  for target in [
``Erdos374.HarmanAnalytic151MeanSquare.exponentialKernel151, ``Erdos374.HarmanAnalytic151MeanSquare.exponentialSum151, ``Erdos374.HarmanAnalytic151MeanSquare.continuous_kernel151, ``Erdos374.HarmanAnalytic151MeanSquare.norm_kernel151, ``Erdos374.HarmanAnalytic151MeanSquare.kernel_zero151, ``Erdos374.HarmanAnalytic151MeanSquare.kernel_mul_conj151, ``Erdos374.HarmanAnalytic151MeanSquare.integral_kernel151, ``Erdos374.HarmanAnalytic151MeanSquare.norm_integral_kernel_le151, ``Erdos374.HarmanAnalytic151MeanSquare.continuous_sum151, ``Erdos374.HarmanAnalytic151MeanSquare.norm_square_expansion151, ``Erdos374.HarmanAnalytic151MeanSquare.mean_square_expansion151, ``Erdos374.HarmanAnalytic151MeanSquare.mean_square_diagonal151, ``Erdos374.HarmanAnalytic151MeanSquare.mean_square_error_le151, ``Erdos374.HarmanAnalytic151MeanSquare.log_difference_lower151, ``Erdos374.HarmanAnalytic151MeanSquare.inverse_log_difference_le151, ``Erdos374.HarmanAnalytic151MeanSquare.inverse_distance_row151, ``Erdos374.HarmanAnalytic151MeanSquare.inverse_log_row151, ``Erdos374.HarmanAnalytic151MeanSquare.quadratic_pair_bound151, ``Erdos374.HarmanAnalytic151MeanSquare.dirichlet_mean_square_error151, ``Erdos374.HarmanAnalytic151MeanSquare.dirichlet_mean_square_le151
] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in retained Harman target {target}"
