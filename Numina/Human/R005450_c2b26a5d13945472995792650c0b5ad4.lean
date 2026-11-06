import Mathlib

open Function
open ZMod

def is_juggling_pattern (j_vals : Array ℕ) (T : ℕ) : Prop :=
  let j : ℕ → ℕ := fun n => j_vals.get! (n % T)
  (∀ n : ℕ, j n ≥ 0) ∧
  let next_ball_landing_time (t : ℕ) : ℕ := t + j (t % T) + 1
  let juggling_function (t : ZMod T) : ZMod T := (next_ball_landing_time t.val) % T
  Bijective juggling_function


theorem numbertheory_608358 : ¬ is_juggling_pattern  #[5, 7, 2] 3 := by
  intro h

  -- Unpack the definition of is_juggling_pattern
  let j_vals := #[5, 7, 2]
  let T := 3
  let j : ℕ → ℕ := fun n => j_vals.get! (n % T)
  have h_nonneg : ∀ n : ℕ, j n ≥ 0 := h.1
  let next_ball_landing_time (t : ℕ) : ℕ := t + j (t % T) + 1
  let juggling_function (t : ZMod T) : ZMod T := (next_ball_landing_time t.val) % T
  -- unfold is_juggling_pattern at h
  -- rcases h

  -- We are interested in the case where T = 3 and j corresponds to the sequence 5, 7, 2.
  have j_zero : j 0 = 5 := by
    unfold j
    rw [Nat.zero_mod]
    decide
  have j_one : j 1 = 7 := by
    unfold j
    norm_num
    decide
  have j_two : j 2 = 2 := by
    unfold j
    norm_num
    decide
  -- To show that it's not a juggling pattern, we need to show that the juggling function is not bijective.
  -- We will show it's not injective by finding two distinct elements in ZMod 3 that map to the same value.

  let t1 : ZMod 3 := 0
  let t2 : ZMod 3 := 1
  have t1_ne_t2 : t1 ≠ t2 := by norm_num

  -- Calculate juggling_function(t1)
  have juggling_function_t1_eq_zero : juggling_function t1 = 0 := by
    unfold juggling_function next_ball_landing_time j j_vals T t1
    norm_num
    tauto

  -- Calculate juggling_function(t2)
  have juggling_function_t2_eq_zero : juggling_function t2 = 0 := by
    unfold juggling_function next_ball_landing_time j j_vals T t2
    norm_num
    tauto

  -- We have juggling_function(t1) = juggling_function(t2) but t1 ≠ t2, so juggling_function is not injective.
  have juggling_function_t1_eq_juggling_function_t2 : juggling_function t1 = juggling_function t2 := by
    rw [juggling_function_t1_eq_zero, juggling_function_t2_eq_zero]

  have not_injective_juggling_function : ¬ Injective juggling_function := by
    intro h_inj
    apply t1_ne_t2
    apply h_inj
    exact juggling_function_t1_eq_juggling_function_t2

  -- Therefore, the juggling function is not bijective, and the given sequence is not a juggling pattern.
  have not_bijective_juggling_function : ¬ Bijective juggling_function := by
    intro h_bij
    exact not_injective_juggling_function h_bij.1

  dsimp[is_juggling_pattern] at h
  tauto
