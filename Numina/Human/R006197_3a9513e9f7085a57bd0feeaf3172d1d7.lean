import Mathlib


/--
Problem statement (Main theorem of this file):
From four cards each written with the functions $y=3x$, $y=x-1$, $y=-2x+2$, and $y=x^2$, two cards are randomly drawn. The sum of the functions on these two cards forms a new function. The probability that this new function is increasing in the first quadrant is ___          ___ .

Solution:
Four functions are numbered ①②③④,\
then ① and ②, ① and ③, ① and ④, ② and ④ are increasing functions in the first quadrant after being added together,\
so the probability $P=\frac{4}{6}=\frac{2}{3}$.

-/

def fns : ℕ → ℝ → ℝ
| 1, x => 3 * x
| 2, x => x - 1
| 3, x => -2 * x + 2
| 4, x => x ^ 2
| _, _ => 0

theorem algebra_634176
  (pairs : Finset (ℕ × ℕ))
  (increasing_pairs : Finset (ℕ × ℕ))
  (hPairs: pairs = {(1,2), (1,3), (1,4), (2,3), (2,4), (3,4)})
  (hIncreasingPairs: increasing_pairs = {p |p ∈ pairs ∧  ∀ x : ℝ, 0 < x → deriv (fun y => fns p.1 y + fns p.2 y) x ≥ 0})
  : increasing_pairs.card / pairs.card = 2 / 3 := by

  have h_1_2:  ∀ x : ℝ, 0 < x → deriv (fun y => fns 1 y + fns 2 y) x ≥ 0 := by
    intro x hx
    unfold fns
    simp
    ring_nf
    rw [deriv_add, deriv_const, deriv_mul_const, deriv_id'']
    . simp
    . simp [differentiableAt_id']
    . simp [differentiableAt_const]
    . simp

  have h_1_3:  ∀ x : ℝ, 0 < x → deriv (fun y => fns 1 y + fns 3 y) x ≥ 0 := by
    intro x hx
    unfold fns
    simp
    ring_nf
    rw [deriv_add, deriv_const, deriv_id'']
    . simp
    . simp [differentiableAt_const]
    . simp [differentiableAt_id']

  have h_1_4:  ∀ x : ℝ, 0 < x → deriv (fun y => fns 1 y + fns 4 y) x ≥ 0 := by
    intro x hx
    unfold fns
    simp
    ring_nf
    rw [deriv_add]
    rw [deriv_mul_const, deriv_id'', deriv_pow]
    simp
    . positivity
    . simp [differentiableAt_id']
    . simp [differentiableAt_pow]
    . simp [differentiableAt_const]

  have h_2_4:  ∀ x : ℝ, 0 < x → deriv (fun y => fns 2 y + fns 4 y) x ≥ 0 := by
    intro x hx
    unfold fns
    simp
    positivity

  have h_2_3_neg:  ¬ (∀ x : ℝ, 0 < x → deriv (fun y => fns 2 y + fns 3 y) x ≥ 0) := by
    by_contra h
    have h_at_1:= h 1
    simp at h_at_1
    unfold fns at h_at_1
    simp at h_at_1
    ring_nf at h_at_1
    rw [deriv_sub, deriv_const, deriv_id''] at h_at_1
    simp at h_at_1
    . linarith
    . simp [differentiableAt_const]
    . simp [differentiableAt_id']

  have h_3_4_neg:  ¬ (∀ x : ℝ, 0 < x → deriv (fun y => fns 3 y + fns 4 y) x ≥ 0) := by
    by_contra h
    have h_at_half:= h (1/2)
    simp at h_at_half
    unfold fns at h_at_half
    simp at h_at_half
    ring_nf at h_at_half
    rw [deriv_add,deriv_sub, deriv_const, deriv_mul_const, deriv_id'', deriv_pow] at h_at_half
    simp at h_at_half
    . simp [differentiableAt_const]
    . simp [differentiableAt_id']
    . simp [differentiableAt_pow]
    . simp [differentiableAt_const]
    . simp [differentiableAt_id']

  have h_inc_pairs_result: increasing_pairs = {(1,2), (1,3), (1,4), (2,4)} := by
    apply Finset.ext
    intro p
    constructor
    . intro hp
      rw [← Finset.mem_coe, hIncreasingPairs, hPairs] at hp
      simp at hp
      simp
      have hp1:= hp.1
      rcases hp1 with rfl | rfl | rfl | rfl | rfl | rfl
      . left; rfl
      . right; left; rfl
      . right; right; left; rfl
      . have := hp.2
        contradiction
      . right; right; right; rfl
      . have := hp.2
        contradiction 
    . intro hp
      rw [← Finset.mem_coe, hIncreasingPairs, hPairs]
      simp
      simp at hp
      rcases hp with rfl | rfl | rfl | rfl
      . constructor
        . left; rfl
        . assumption
      . constructor
        . right; left; rfl
        . assumption
      . constructor
        . right; right; left; rfl
        . assumption
      . constructor
        . right; right; right; right; left; rfl
        . assumption

  rw [h_inc_pairs_result, hPairs]
  decide
  