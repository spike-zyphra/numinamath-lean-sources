import Mathlib

def S: Set ℕ := {1, 2, 4, 8, 16, 20}

-- we first tackle the case when a < b < c
lemma lemma_1 (a b c: ℕ) (ha: a ∈ S) (hb: b ∈ S) (hc: c ∈ S)
  (h1: a < b) (h2: b < c) (h3: a * b * c = 40): a + b + c = 23 := by

  set A:= S \ {16}
  have hA: A = {1, 2, 4, 8, 20} := by
    simp [A, S]
    ext x
    simp
    omega

  -- first show that a, b, c are not 16, hence they are in A
  replace ha: a ∈ A := by
    simp [A, ha]
    by_contra! o
    simp [o] at h3
    replace h3: 16 ∣ 40 := by
      rw [← h3]
      rw [show 16 * b * c = 16 * (b * c) by ring]
      simp
    norm_num at h3
  replace hb: b ∈ A := by
    simp [A, hb]
    by_contra! o
    simp [o] at h3
    replace h3: 16 ∣ 40 := by
      rw [← h3]
      rw [show a * 16 * c = 16 * (a * c) by ring]
      simp
    norm_num at h3
  replace hc: c ∈ A := by
    simp [A, hc]
    by_contra! o
    simp [o] at h3
    replace h3: 16 ∣ 40 := by
      rw [← h3]
      rw [show a * b * 16 = 16 * (a * b) by ring]
      simp
    norm_num at h3
  clear_value A

  simp [hA] at ha hb hc
  rcases ha with i | i | i | i | i <;> rcases hb with j | j | j | j | j <;> rcases hc with k | k | k | k | k <;> simp [i, j, k] at *

/-Let S be the set of integers {1,2,4,8,16,20}.
Suppose three distinct integers
a,b,c from the set S have a product equal to a given integer
P 0. If P 0 =40, show that the sum of these three integers a+b+c is -/

theorem number_theory_634639 {a b c P0: ℕ} (ha: a ∈ S) (hb: b ∈ S) (hc: c ∈ S)
  (h1: a ≠ b) (h2: a ≠ c) (h3: b ≠ c) (h4: a * b * c = P0) (h5: P0 = 40): a + b + c = 23 := by

  simp [h5] at h4
  clear h5
  have u: a < b ∧ b < c ∨ a < c ∧ c < b ∨ b < a ∧ a < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b ∨ c < b ∧ b < a := by
    omega
  rcases u with u | u | u | u | u | u

  -- case 1: a < b ∧ b < c
  .
    exact lemma_1 a b c ha hb hc (by omega) (by omega) (by omega)

  -- case 2: a < c ∧ c < b
  .
    rw [show a * b * c = a * c * b by ring] at h4
    have i:= lemma_1 a c b ha hc hb (by omega) (by omega) (by omega)
    linarith

  -- case 3: b < a ∧ a < c
  .
    rw [show a * b * c = b * a * c by ring] at h4
    have i:= lemma_1 b a c hb ha hc (by omega) (by omega) (by omega)
    linarith

  -- case 4: b < c ∧ c < a
  .
    rw [show a * b * c = b * c * a by ring] at h4
    have i:= lemma_1 b c a hb hc ha (by omega) (by omega) (by omega)
    linarith

  -- case 5: c < a ∧ a < b
  .
    rw [show a * b * c = c * a * b by ring] at h4
    have i:= lemma_1 c a b hc ha hb (by omega) (by omega) (by omega)
    linarith

  -- case 6: c < b ∧ b < a
  .
    rw [show a * b * c = c * b * a by ring] at h4
    have i:= lemma_1 c b a hc hb ha (by omega) (by omega) (by omega)
    linarith
