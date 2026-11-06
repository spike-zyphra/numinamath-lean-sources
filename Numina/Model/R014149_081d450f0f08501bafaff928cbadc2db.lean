import Mathlib

theorem number_theory_136524 (S : ℕ) (hS : S = ∑ i in Finset.Icc 1 2012, i) (hS1 : 2011 ∣ S)
    (A : ℕ) (hA : A = ∑ i in Finset.Icc 1 2013, i) (hA1 : 2014 ∣ A) :
    (A - S) / (A - S - 2012) = 2 / 3 := by
  have h1 : S = 2012 * 2013 / 2 := by 
    rw [hS]
    native_decide
  have h2 : A = 2013 * 2014 / 2 := by
    rw [hA]
    native_decide
  have h3 : A - S = 2013 := by
    calc 
      A - S = (2013 * 2014 / 2) - (2012 * 2013 / 2) := by 
        rw [h1, h2]
      _ = 2013 := by
        norm_num
        <;> try omega
  have h4 : (A - S - 2012) = 1 := by
    omega
  have h5 : (A - S) / (A - S - 2012) = 2013 := by 
    rw [h4]
    norm_num 
    <;> try { omega }
  have eq0 : (A - S) / (A - S - 2012) = 2013 := h5
  have h6 : (2013 : ℕ) = 2013 := by rfl 
  rw [eq0] 
  all_goals norm_num 
  <;> try { omega }