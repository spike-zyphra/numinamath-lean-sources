import Mathlib
open Nat Rat

/-Bob writes a random string of 5 letters, where each letter is either $A, B, C$, or $D$. The letter in each position is independently chosen, and each of the letters $A, B, C, D$ is chosen with equal probability. Given that there are at least two $A$ 's in the string, find the probability that there are at least three $A$ 's in the string.
-/

-- Length of the string
def string_length : ℕ := 5

-- Number of non-A letters
def num_other_letters : ℕ := 3

-- Function to calculate the number of strings with exactly k A's
-- C(N_A = k) = (string_length choose k) * (num_other_letters ^ (string_length - k))
def count_strings_exact_A (k : ℕ) : ℕ :=
  if k ≤ string_length then
    (Nat.choose string_length k) * (num_other_letters ^ (string_length - k))
  else
    0 -- Cannot have more A's than the string length

-- Calculate counts for specific numbers of A's
lemma count_strings_2_A : count_strings_exact_A 2 = 270 := by
  unfold count_strings_exact_A string_length num_other_letters
  simp only [show 2 ≤ 5 by norm_num, if_true] -- k ≤ string_length
  have h_choose : Nat.choose 5 2 = 10 := by rfl
  rw [h_choose]
  have h_pow : 3 ^ (5 - 2) = 3 ^ 3 := by norm_num
  rw [h_pow]
  norm_num 

lemma count_strings_3_A : count_strings_exact_A 3 = 90 := by
  unfold count_strings_exact_A string_length num_other_letters
  simp only [show 3 ≤ 5 by norm_num, if_true]
  have h_choose : Nat.choose 5 3 = 10 := by decide
  rw [h_choose]
  have h_pow : 3 ^ (5 - 3) = 3 ^ 2 := by norm_num
  rw [h_pow]
  norm_num 

lemma count_strings_4_A : count_strings_exact_A 4 = 15 := by
  unfold count_strings_exact_A string_length num_other_letters
  simp only [show 4 ≤ 5 by norm_num, if_true]
  have h_choose : Nat.choose 5 4 = 5 := by norm_num
  rw [h_choose]
  have h_pow : 3 ^ (5 - 4) = 3 ^ 1 := by norm_num
  rw [h_pow]
  norm_num 

lemma count_strings_5_A : count_strings_exact_A 5 = 1 := by
  unfold count_strings_exact_A string_length num_other_letters
  simp only [show 5 ≤ 5 by norm_num, if_true]
  have h_choose : Nat.choose 5 5 = 1 := by norm_num
  rw [h_choose]
  have h_pow : 3 ^ (5 - 5) = 3 ^ 0 := by norm_num
  rw [h_pow, pow_zero] 
  norm_num 

-- Number of strings with at least 3 A's
def count_at_least_3_A : ℕ :=
  count_strings_exact_A 3 + count_strings_exact_A 4 + count_strings_exact_A 5

lemma count_at_least_3_A_val : count_at_least_3_A = 106 := by
  unfold count_at_least_3_A
  rw [count_strings_3_A, count_strings_4_A, count_strings_5_A]


-- Number of strings with at least 2 A's
def count_at_least_2_A : ℕ :=
  count_strings_exact_A 2 + count_strings_exact_A 3 + count_strings_exact_A 4 + count_strings_exact_A 5

lemma count_at_least_2_A_val : count_at_least_2_A = 376 := by
  unfold count_at_least_2_A
  rw [count_strings_2_A, count_strings_3_A, count_strings_4_A, count_strings_5_A]

-- The conditional probability P(N_A ≥ 3 | N_A ≥ 2) = C(N_A ≥ 3) / C(N_A ≥ 2)
def conditional_probability : ℚ :=
  (↑count_at_least_3_A : ℚ) / (↑count_at_least_2_A : ℚ)

theorem combinatorics_609223 :
    conditional_probability = (53 : ℚ) / 188 := by
  unfold conditional_probability
  rw [count_at_least_3_A_val, count_at_least_2_A_val]
  norm_cast 
  have h_num : (106 : ℚ) = 2 * 53 := by norm_num
  have h_den : (376 : ℚ) = 2 * 188 := by norm_num
  rw [h_num, h_den]
  norm_num

