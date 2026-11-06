import Mathlib

theorem number_theory_127934 {a b : ℤ} (hcoprime : IsCoprime a b) :
    IsCoprime (a * b) (a + b) := by 
  have h1 : IsCoprime a (a + b) := by 
    have h4 : IsCoprime a b := hcoprime
    rcases h4 with ⟨x, y, h_eq⟩ 
    use (x - y)
    use y 
    linarith 
  have h2 : IsCoprime b (a + b) := by 
    have h3 : IsCoprime a b := hcoprime 
    rcases h3 with ⟨x, y, h_eq⟩ 
    use (y - x) 
    use x 
    linarith 
  -- Now we have IsCoprime a (a+b) and IsCoprime b (a+b)
  -- We need IsCoprime (a * b) (a + b)
  have h3 : IsCoprime (a * b) (a + b) := by 
    have h4 : IsCoprime a (a + b) := h1 
    have h5 : IsCoprime b (a + b) := h2 
    have h6 := IsCoprime.mul_left h4 h5 
    exact h6 
  exact h3