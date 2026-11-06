import Mathlib

def isPrime (n : ℕ) := n > 1 ∧ ∀ m, m ∣ n → m = 1 ∨ m = n

theorem number_theory_170957 :
    isPrime 2 ∧ isPrime 3 ∧ isPrime 5 ∧ isPrime 7 ∧ isPrime 11 ∧ isPrime 13 ∧
    isPrime 17 ∧ isPrime 19 ∧ isPrime 23 ∧ isPrime 29 ∧ isPrime 31 ∧ isPrime 37 ∧
    isPrime 41 ∧ isPrime 43 ∧ isPrime 47 ∧ isPrime 53 ∧ isPrime 59 ∧ isPrime 61 ∧
    isPrime 67 ∧ isPrime 71 ∧ isPrime 73 ∧ isPrime 79 := by

  have h2 : isPrime 2 := by 
    unfold isPrime
    constructor
    · norm_num
    · intro m h 
      have h1 : m ≤ 2 := by 
        exact Nat.le_of_dvd (by norm_num) h
      interval_cases m <;> norm_num at h ⊢

  have h3 : isPrime 3 := by 
    unfold isPrime
    constructor 
    · norm_num
    · intro m h
      have h1 : m ≤ 3 := by
        exact Nat.le_of_dvd (by norm_num) h 
      interval_cases m <;> norm_num at h ⊢

  have h5 : isPrime 5 := by 
    unfold isPrime
    constructor 
    · norm_num 
    · intro m h 
      have h1 : m ≤ 5 := by
        exact Nat.le_of_dvd (by norm_num) h
      interval_cases m <;> norm_num at h ⊢

  have h7 : isPrime 7 := by
    unfold isPrime 
    constructor 
    · norm_num 
    · intro m h 
      have h1 : m ≤ 7 := by
        exact Nat.le_of_dvd (by norm_num) h 
      interval_cases m <;> norm_num at h ⊢

  have h11 : isPrime 11 := by 
    unfold isPrime
    constructor 
    · norm_num 
    · intro m h 
      have h1 : m ≤ 11 := by
        exact Nat.le_of_dvd (by norm_num) h
      interval_cases m <;> norm_num at h ⊢

  have h13 : isPrime 13 := by
    unfold isPrime
    constructor
    · norm_num 
    · intro m h 
      have h1 : m ≤ 13 := by
        exact Nat.le_of_dvd (by norm_num) h
      interval_cases m <;> norm_num at h ⊢

  have h17 : isPrime 17 := by 
    unfold isPrime
    constructor 
    · norm_num 
    · intro m h 
      have h1 : m ≤ 17 := by
        exact Nat.le_of_dvd (by norm_num) h
      interval_cases m <;> norm_num at h ⊢

  have h19 : isPrime 19 := by 
    unfold isPrime
    constructor 
    · norm_num 
    · intro m h 
      have h1 : m ≤ 19 := by
        exact Nat.le_of_dvd (by norm_num) h 
      interval_cases m <;> norm_num at h ⊢

  have h23 : isPrime 23 := by
    unfold isPrime 
    constructor 
    · norm_num 
    · intro m h
      have h1 : m ≤ 23 := by 
        exact Nat.le_of_dvd (by norm_num) h 
      interval_cases m <;> norm_num at h ⊢

  have h29 : isPrime 29 := by
    unfold isPrime 
    constructor 
    · norm_num 
    · intro m h
      have h1 : m ≤ 29 := by 
        exact Nat.le_of_dvd (by norm_num) h 
      interval_cases m <;> norm_num at h ⊢

  have h31 : isPrime 31 := by
    unfold isPrime 
    constructor 
    · norm_num 
    · intro m h 
      have h1 : m ≤ 31 := by 
        exact Nat.le_of_dvd (by norm_num) h 
      interval_cases m <;> norm_num at h ⊢

  have h37 : isPrime 37 := by 
    unfold isPrime 
    constructor
    · norm_num 
    · intro m h
      have h1 : m ≤ 37 := by
        exact Nat.le_of_dvd (by norm_num) h 
      interval_cases m <;> norm_num at h ⊢

  have h41 : isPrime 41 := by 
    unfold isPrime 
    constructor 
    · norm_num 
    · intro m h
      have h1 : m ≤ 41 := by 
        exact Nat.le_of_dvd (by norm_num) h 
      interval_cases m <;> norm_num at h ⊢

  have h43 : isPrime 43 := by 
    unfold isPrime 
    constructor 
    · norm_num 
    · intro m h
      have h1 : m ≤ 43 := by 
        exact Nat.le_of_dvd (by norm_num) h 
      interval_cases m <;> norm_num at h ⊢

  have h47 : isPrime 47 := by 
    unfold isPrime 
    constructor 
    · norm_num 
    · intro m h
      have h1 : m ≤ 47 := by
        exact Nat.le_of_dvd (by norm_num) h 
      interval_cases m <;> norm_num at h ⊢

  have h53 : isPrime 53 := by 
    unfold isPrime 
    constructor 
    · norm_num 
    · intro m h 
      have h1 : m ≤ 53 := by 
        exact Nat.le_of_dvd (by norm_num) h 
      interval_cases m <;> norm_num at h ⊢

  have h59 : isPrime 59 := by 
    unfold isPrime 
    constructor 
    · norm_num 
    · intro m h 
      have h1 : m ≤ 59 := by 
        exact Nat.le_of_dvd (by norm_num) h 
      interval_cases m <;> norm_num at h ⊢

  have h61 : isPrime 61 := by 
    unfold isPrime 
    constructor 
    · norm_num
    · intro m h 
      have h1 : m ≤ 61 := by 
        exact Nat.le_of_dvd (by norm_num) h 
      interval_cases m <;> norm_num at h ⊢

  have h67 : isPrime 67 := by 
    unfold isPrime 
    constructor 
    · norm_num 
    · intro m h 
      have h1 : m ≤ 67 := by
        exact Nat.le_of_dvd (by norm_num) h 
      interval_cases m <;> norm_num at h ⊢

  have h71 : isPrime 71 := by
    unfold isPrime 
    constructor 
    · norm_num 
    · intro m h 
      have h1 : m ≤ 71 := by
        exact Nat.le_of_dvd (by norm_num) h 
      interval_cases m <;> norm_num at h ⊢

  have h73 : isPrime 73 := by
    unfold isPrime
    constructor 
    · norm_num 
    · intro m h 
      have h1 : m ≤ 73 := by 
        exact Nat.le_of_dvd (by norm_num) h 
      interval_cases m <;> norm_num at h ⊢

  have h79 : isPrime 79 := by 
    unfold isPrime 
    constructor 
    · norm_num 
    · intro m h 
      have h1 : m ≤ 79 := by 
        exact Nat.le_of_dvd (by norm_num) h 
      interval_cases m <;> norm_num at h ⊢

  exact ⟨h2, h3, h5, h7, h11, h13, h17, h19, h23, h29, h31, h37, h41, h43, h47, h53, h59, h61, h67, h71, h73, h79⟩