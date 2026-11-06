import Mathlib

/-!
Let $n$ be the answer to this problem. We define the digit sum of a date as the sum of its 4 digits when expressed in mmdd format (e.g. the digit sum of 13 May is $0+5+1+3=9$ ). Find the number of dates in the year 2021 with digit sum equal to the positive integer $n$.
-/

namespace DigitSumDate

def digitSum₂ (n : ℕ) : ℕ := (n / 10) + (n % 10)

def dateDigitSum (m d : ℕ) : ℕ := digitSum₂ m + digitSum₂ d

def daysInMonth (month : ℕ) : ℕ :=
  match month with
  | 1  => 31 | 7  => 31
  | 2  => 28 | 8  => 31
  | 3  => 31 | 9  => 30
  | 4  => 30 | 10 => 31
  | 5  => 31 | 11 => 30
  | 6  => 30 | 12 => 31
  | _  => 0 -- Invalid months have 0 days

/--
A list of all valid dates (month, day) in 2021.
-/
def allDates2021 : List (ℕ × ℕ) :=
  (List.range 12).flatMap (fun m_idx =>
    let month := m_idx + 1
    (List.range (daysInMonth month)).map (fun d_idx => (month, d_idx + 1))
  )

-- The total number of days in 2021 should be 365.
lemma card_allDates2021 : List.length allDates2021 = 365 := by
  native_decide

def N (k : ℕ) : ℕ :=
  (allDates2021.filter (fun (m, d) => dateDigitSum m d = k)).length

lemma N_1_eq_0     : N  1 =  0 := by rfl
lemma N_2_eq_4     : N  2 =  4 := by rfl
lemma N_3_eq_10    : N  3 = 10 := by rfl
lemma N_4_eq_18    : N  4 = 18 := by rfl
lemma N_5_eq_23    : N  5 = 23 := by rfl
lemma N_6_eq_25    : N  6 = 25 := by rfl
lemma N_7_eq_29    : N  7 = 29 := by rfl
lemma N_8_eq_30    : N  8 = 30 := by rfl
lemma N_9_eq_34    : N  9 = 34 := by rfl
lemma N_10_eq_36   : N 10 = 36 := by rfl
lemma N_11_eq_36   : N 11 = 36 := by rfl
lemma N_12_eq_32   : N 12 = 32 := by rfl
lemma N_13_eq_26   : N 13 = 23 := by rfl
lemma N_14_eq_19   : N 14 = 19 := by rfl
lemma N_15_eq_15   : N 15 = 15 := by rfl
lemma N_16_eq_12   : N 16 = 12 := by rfl
lemma N_17_eq_9    : N 17 =  9 := by rfl
lemma N_18_eq_6    : N 18 =  6 := by rfl
lemma N_19_eq_3    : N 19 =  3 := by rfl
lemma N_20_eq_1    : N 20 =  1 := by rfl

theorem combinatorics_610395 : ∀ (n : ℕ), n > 0 → (N n = n ↔ n = 15) := by
  intro n hn_pos
  constructor
  -- Direction `N n = n → n = 15`.
  -- We prove this by a case analysis on `n`.
  intro h_Nn_eq_n
  -- We know `n` must be in the range [2, 20] for `N n` to be non-zero.
  -- The following case split handles all positive `n`.
  match n with
  | 1 => rw[N_1_eq_0] at h_Nn_eq_n; linarith
  | 2 => rw [N_2_eq_4] at h_Nn_eq_n; contradiction
  | 3 => rw [N_3_eq_10] at h_Nn_eq_n; contradiction
  | 4 => rw [N_4_eq_18] at h_Nn_eq_n; contradiction
  | 5 => rw [N_5_eq_23] at h_Nn_eq_n; contradiction
  | 6 => rw [N_6_eq_25] at h_Nn_eq_n; contradiction
  | 7 => rw [N_7_eq_29] at h_Nn_eq_n; contradiction
  | 8 => rw [N_8_eq_30] at h_Nn_eq_n; contradiction
  | 9 => rw [N_9_eq_34] at h_Nn_eq_n; contradiction
  | 10 => rw [N_10_eq_36] at h_Nn_eq_n; contradiction
  | 11 => rw [N_11_eq_36] at h_Nn_eq_n; contradiction
  | 12 => rw [N_12_eq_32] at h_Nn_eq_n; contradiction
  | 13 => rw [N_13_eq_26] at h_Nn_eq_n; contradiction
  | 14 => rw [N_14_eq_19] at h_Nn_eq_n; contradiction
  | 15 => rfl -- This is the only non-contradictory case.
  | 16 => rw [N_16_eq_12] at h_Nn_eq_n; contradiction
  | 17 => rw [N_17_eq_9] at h_Nn_eq_n; contradiction
  | 18 => rw [N_18_eq_6] at h_Nn_eq_n; contradiction
  | 19 => rw [N_19_eq_3] at h_Nn_eq_n; contradiction
  | 20 => rw [N_20_eq_1] at h_Nn_eq_n; contradiction
  | k + 21 => 
    have h_N_zero : N (k + 21) = 0 := by rfl
    rw [h_N_zero] at h_Nn_eq_n
    linarith
    
  intro h_n_is_15
  rw [h_n_is_15] 
  exact N_15_eq_15

end DigitSumDate
