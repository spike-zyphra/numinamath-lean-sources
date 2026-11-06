import Mathlib

theorem number_theory_224105 (a : Fin 18 → ℕ) (ha : StrictMono a)
    (hsum : ∑ i, a i = 2001) (ha' : ∀ i, 0 < a i) :
    a 8 ≤ 192 := by 
  have h1 : a 0 ≥ 1 := by 
    have : 0 < a 0 := ha' 0
    linarith
  have h2 : a 1 > a 0 := by apply ha; simp
  have h2' : a 1 ≥ a 0 + 1 := by omega
  have h3 : a 2 > a 1 := by apply ha; simp
  have h3' : a 2 ≥ a 1 + 1 := by omega
  have h4 : a 3 > a 2 := by apply ha; simp
  have h4' : a 3 ≥ a 2 + 1 := by omega
  have h5 : a 4 > a 3 := by apply ha; simp
  have h5' : a 4 ≥ a 3 + 1 := by omega
  have h6 : a 5 > a 4 := by apply ha; simp
  have h6' : a 5 ≥ a 4 + 1 := by omega
  have h7 : a 6 > a 5 := by apply ha; simp
  have h7' : a 6 ≥ a 5 + 1 := by omega
  have h8 : a 7 > a 6 := by apply ha; simp
  have h8' : a 7 ≥ a 6 + 1 := by omega
  have h10 : a 9 > a 8 := by apply ha; simp
  have h10' : a 9 ≥ a 8 + 1 := by omega
  have h11 : a 10 > a 9 := by apply ha; simp
  have h11' : a 10 ≥ a 9 + 1 := by omega
  have h12 : a 11 > a 10 := by apply ha; simp
  have h12' : a 11 ≥ a 10 + 1 := by omega
  have h13 : a 12 > a 11 := by apply ha; simp
  have h13' : a 12 ≥ a 11 + 1 := by omega
  have h14 : a 13 > a 12 := by apply ha; simp
  have h14' : a 13 ≥ a 12 + 1 := by omega
  have h15 : a 14 > a 13 := by apply ha; simp
  have h15' : a 14 ≥ a 13 + 1 := by omega
  have h16 : a 15 > a 14 := by apply ha; simp
  have h16' : a 15 ≥ a 14 + 1 := by omega
  have h17 : a 16 > a 15 := by apply ha; simp
  have h17' : a 16 ≥ a 15 + 1 := by omega
  have h18 : a 17 > a 16 := by apply ha; simp
  have h18' : a 17 ≥ a 16 + 1 := by omega
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at hsum ⊢
  linarith [hsum, h1, h2', h3', h4', h5', h6', h7', h8', 
          h10', h11', h12', h13', h14', h15', h16', h17', h18']