import Mathlib
open Nat
def ProblemS1UKR : Prop :=
  ∃ F : ℕ → ℕ,
    (∀ k : ℕ, ∃ n : ℕ, n ≥ 1 ∧ F n = k) ∧
    (∀ k : ℕ, k > 0 → (∀ M : ℕ, ∃ n : ℕ, n > M ∧ F n = k)) ∧
    (∀ n_arg : ℕ, n_arg ≥ 2 → F (F (n_arg ^ 163)) = F (F n_arg) + F (F 361))
def ConditionA (F : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ n : ℕ, n ≥ 1 ∧ F n = k
def ConditionB (F : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, k > 0 → (∀ M : ℕ, ∃ n : ℕ, n > M ∧ F n = k)
def ConditionC (F : ℕ → ℕ) : Prop :=
  ∀ n_arg : ℕ, n_arg ≥ 2 → F (F (n_arg ^ 163)) = F (F n_arg) + F (F 361)
def F_sol2 (n : ℕ) : ℕ := ArithmeticFunction.cardFactors n
lemma mypos_iff_ne_zero (n: ℕ) : n > 0 ↔ n ≠ 0 := by
  apply Iff.intro
  · intro h
    exact Nat.ne_of_gt h
  · intro h
    exact Nat.pos_of_ne_zero h
lemma ArithmeticFunction.cardFactors_ne_zero_of_ge_two (n_arg : ℕ) (hn_arg_ge_2 : n_arg ≥ 2) :
    ArithmeticFunction.cardFactors n_arg ≠ 0 := by
  rw [ArithmeticFunction.cardFactors_apply]
  rw [← mypos_iff_ne_zero]
  simp [List.length_pos_iff_ne_nil]
  omega
lemma ArithmeticFunction.cardFactors_eq_sum_factorization (n : ℕ) :
    ArithmeticFunction.cardFactors n = n.factorization.sum (fun p e => e) := by
  simp [ArithmeticFunction.cardFactors_apply]
  rw [← List.sum_toFinset_count_eq_length]
  rw [Nat.toFinset_factors]
  apply Finset.sum_congr rfl
  intro p hp_in_primeFactors
  exact Nat.primeFactorsList_count_eq
lemma ArithmeticFunction.cardFactors_pow' (n k : ℕ) :
    ArithmeticFunction.cardFactors (n^k) = k * ArithmeticFunction.cardFactors n := by
  simp [ArithmeticFunction.cardFactors_eq_sum_factorization]
  rw [Finsupp.sum_smul_index']
  simp_rw [smul_eq_mul]
  unfold Finsupp.sum
  simp [Nat.support_factorization]
  rw [Finset.mul_sum]
  simp [implies_true]
lemma conditionA_sol2_holds :
  ∀ k : ℕ, ∃ n : ℕ, n ≥ 1 ∧ F_sol2 n = k := by
  intro k
  use (2^k)
  constructor
  have h1 : 0 < 2 ^ k := by
    apply Nat.pow_pos
    all_goals norm_num
  linarith
  simp [F_sol2]
  apply ArithmeticFunction.cardFactors_apply_prime_pow
  norm_num
lemma conditionB_sol2_holds :
  ∀ k : ℕ, k > 0 → (∀ M : ℕ, ∃ n : ℕ, n > M ∧ F_sol2 n = k) :=by
  intros k hk M
  let p0_val := Nat.nth Nat.Prime 0
  let rest_primes_list := (List.range (k-1)).map (fun i => Nat.nth Nat.Prime (i+1))
  let rest_prod := rest_primes_list.prod
  have hp0_gt_one : p0_val > 1 := by
    simp [p0_val]
  have h_pow_tendsto_atTop : Filter.Tendsto (fun j : ℕ => p0_val^(j+1)) Filter.atTop Filter.atTop :=by
    apply Filter.Tendsto.comp
    · apply Nat.tendsto_pow_atTop_atTop_of_one_lt
      exact hp0_gt_one
    · 
      apply Filter.tendsto_add_atTop_nat
  have h_rest_prod_pos : rest_prod > 0 := by
    cases k 
    · exact absurd hk (Nat.not_lt_zero 0) 
    · rename_i k' 
      simp [p0_val, rest_prod, rest_primes_list]
      intro a a_1
      have h_prime : Nat.Prime (nth Nat.Prime (a+1)) := Nat.prime_nth_prime (a+1)
      exact Nat.Prime.pos h_prime
  have pow_tend_to_infinity : Filter.Tendsto (fun x : ℕ => x^k) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_pow_atTop
    linarith
  have primes_tend_to_infinity : Filter.Tendsto (fun j : ℕ => Nat.nth Nat.Prime j) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro M
    simp
    use M
    intro j hj_ge_M
    have hh: M < nth Nat.Prime j:= by
      calc
        M ≤ j := hj_ge_M                       
        _ < j + 2 := by linarith               
        _ ≤ nth Nat.Prime j := Nat.add_two_le_nth_prime j
    linarith
  have n_j_tend_to_infinity : Filter.Tendsto (fun j : ℕ => (Nat.nth Nat.Prime j)^k) Filter.atTop Filter.atTop := by
    exact Filter.Tendsto.comp pow_tend_to_infinity primes_tend_to_infinity
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, ∀ (j : ℕ), J ≤ j → M < (Nat.nth Nat.Prime j)^k :=
    Filter.tendsto_atTop_atTop.mp n_j_tend_to_infinity (M + 1)
  let n_val := (Nat.nth Nat.Prime J)^k
  use n_val
  constructor
  · 
    apply hJ J (le_refl J)
  · 
    simp only [F_sol2, n_val]
    have h_prime_nth : Nat.Prime (Nat.nth Nat.Prime J) := Nat.prime_nth_prime J
    apply ArithmeticFunction.cardFactors_apply_prime_pow h_prime_nth
lemma conditionC_sol2_holds :
  ∀ n_arg : ℕ, n_arg ≥ 2 →
    F_sol2 (F_sol2 (n_arg ^ 163)) = F_sol2 (F_sol2 n_arg) + F_sol2 (F_sol2 361) := by
  intros n_arg hn_arg_ge_2
  simp only [F_sol2]
  have h_rhs_const : ArithmeticFunction.cardFactors (ArithmeticFunction.cardFactors 361) = 1 := by
    have h361 : 361 = 19^2 := by norm_num
    rw [h361]
    have h_prime_19 : Nat.Prime 19 := by norm_num
    have h_card_factors_361 : ArithmeticFunction.cardFactors (19^2) = 2 :=
      ArithmeticFunction.cardFactors_apply_prime_pow h_prime_19
    rw [h_card_factors_361]
    have h_prime_2 : Nat.Prime 2 := by norm_num
    rw [ArithmeticFunction.cardFactors_eq_one_iff_prime]
    exact h_prime_2
  rw [h_rhs_const]
  let val_n := ArithmeticFunction.cardFactors n_arg
  have h_card_factors_pow : ArithmeticFunction.cardFactors (n_arg ^ 163) = 163 * val_n := by
    apply ArithmeticFunction.cardFactors_pow'
  rw [h_card_factors_pow]
  have h_card_factors_mul : ArithmeticFunction.cardFactors (163 * val_n) = ArithmeticFunction.cardFactors 163 + ArithmeticFunction.cardFactors val_n := by
    apply ArithmeticFunction.cardFactors_mul
    norm_num 
    unfold val_n
    apply ArithmeticFunction.cardFactors_ne_zero_of_ge_two
    exact hn_arg_ge_2
  rw [h_card_factors_mul]
  have h_card_factors_163 : ArithmeticFunction.cardFactors 163 = 1 := by
    have h_prime_163 : Nat.Prime 163 := by norm_num 
    rw [ArithmeticFunction.cardFactors_eq_one_iff_prime]
    exact h_prime_163
  rw [h_card_factors_163]
  rw [add_comm (ArithmeticFunction.cardFactors val_n) 1] 
def problem_S1_UKR_solution_exists : ProblemS1UKR :=
  ⟨F_sol2, conditionA_sol2_holds, conditionB_sol2_holds, conditionC_sol2_holds⟩
theorem other_24626 : ∃ F : ℕ → ℕ, ConditionA F ∧ ConditionB F ∧ ConditionC F := by
  use F_sol2
  constructor
  · 
    exact conditionA_sol2_holds
  · constructor
    · 
      exact conditionB_sol2_holds
    · 
      exact conditionC_sol2_holds