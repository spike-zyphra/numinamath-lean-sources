import Mathlib

theorem number_theory_236800 (a b c : ℕ) (ha : a ∈ Finset.Icc 1000 9999)
    (hb : b ∈ Finset.Icc 1000 9999) (hc : c ∈ Finset.Icc 1000 9999)
    (h1 : ∀ i ∈ Finset.range 4, (a / 10 ^ i) % 10 < (a / 10 ^ (i + 1)) % 10)
    (h2 : ∀ i ∈ Finset.range 4, (b / 10 ^ i) % 10 > (b / 10 ^ (i + 1)) % 10)
    (h3 : a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (h4 : a + b + c = 26352) :
    a = 6789 := by
  norm_num [Finset.mem_Icc] at ha hb hc ⊢
  have ha1 := h1 0 (by norm_num)
  have ha2 := h1 1 (by norm_num)
  have ha3 := h1 2 (by norm_num)
  have ha4 := h1 3 (by norm_num)
  have hb1 := h2 0 (by norm_num)
  have hb2 := h2 1 (by norm_num)
  have hb3 := h2 2 (by norm_num)
  have hb4 := h2 3 (by norm_num)
  omega