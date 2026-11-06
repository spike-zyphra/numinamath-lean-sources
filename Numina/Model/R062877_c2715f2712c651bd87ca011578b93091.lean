import Mathlib

def sumOfDigits (n : ℕ) := (Nat.digits 10 n).sum

def isWonderful (n : ℕ) :=
  sumOfDigits n = sumOfDigits (3 * n) ∧ ¬sumOfDigits n = sumOfDigits (2 * n)

theorem number_theory_149374 :
    IsLeast {n | isWonderful n} 144 := by
  constructor
  · -- Show 144 is a wonderful number
    show isWonderful 144
    unfold isWonderful sumOfDigits
    all_goals norm_num
  · -- Show that 144 is the smallest
    intro n hn
    have h1 : isWonderful n := hn
    unfold isWonderful at h1
    -- Use the definition of isWonderful
    rcases h1 with ⟨h_eq, h_ne⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num [sumOfDigits] at h_eq h_ne <;> all_goals
      try { contradiction } <;> try { trivial } <;> try { norm_num at h_eq h_ne; all_goals try { contradiction } }
    <;> try { trivial } <;> try { norm_num at h_eq h_ne; all_goals try { contradiction } }
    <;> try { trivial } <;> try { contradiction }
    all_goals try { omega }
    all_goals try { trivial } <;> try { contradiction }
    all_goals try { try { tauto } }