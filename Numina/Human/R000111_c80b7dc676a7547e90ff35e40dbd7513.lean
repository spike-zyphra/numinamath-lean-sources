import Mathlib 

/-- If $\( a, b, m, \)$ and $\( n \)$ are integers, and if $\( c \)$ divides $\( a \)$ and $\( c \)$ divides $\( b \)$, then $\( c \)$ also divides $\( (m a + n b) \)$.-/
theorem number_theory_4638 (a b c m n : ℤ) (h1 : c ∣ a) (h2 : c ∣ b)
  : c ∣ m * a + n * b := 
  -- use `Dvd.dvd.linear_comb` which says that 
  -- if $a \mid b$ and $a \mid c$, then $a$ divides the linear combination of $b$ and $c$.
  Dvd.dvd.linear_comb h1 h2 m n