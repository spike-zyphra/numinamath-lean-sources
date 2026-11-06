import Mathlib

theorem  algebra_297840 (m : ℤ) (hm : m > 0) (h : ∃ k, k^2 = m^2 + 5 * m + 30) : m = 21 ∨ m = 1 := by 
  obtain ⟨k,hk⟩ := h

  wlog kpos : 0 ≤ k
  have kneg : k ≤ 0 := by linarith
  have t: 0 ≤ -k := by linarith
  have eq2: (-k)^2 = m^2 + 5 * m + 30 := by linarith
  apply this
  exact hm
  exact eq2
  exact t

  --Note that m^2 + 5m + 30 is between (m+2)^2 and (m+6)^2
  --We have that k is between m+3 and m+5. 
  --We just need to check every case.
  have : 0 < m+2 := by nlinarith

  have : (m+2)^2 < m^2 + 5*m + 30 := by nlinarith
  have : m+2 < k := by nlinarith
  have : m^2 + 5 * m + 30 < (m+6)^2 := by nlinarith
  have : k < m+6 := by nlinarith

  by_cases kem3 : k = m + 3
  rw [kem3] at hk
  ring_nf at hk
  field_simp at hk
  left
  omega
  by_cases kem4 : k = m + 4
  rw [kem4] at hk
  ring_nf at hk
  field_simp at hk
  exfalso; omega
  have kem5 : k = m + 5 := by omega
  rw [kem5] at hk
  ring_nf at hk
  field_simp at hk
  right; omega
