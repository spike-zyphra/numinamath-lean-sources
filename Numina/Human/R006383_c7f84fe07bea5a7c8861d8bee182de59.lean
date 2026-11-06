import Mathlib

/- Let $N_0=20$. The factorial $N_0!$ is a 19-digit number.
Suppose its decimal representation is given by $24329020x8176y40000$,
where $x$ and $y$ are unknown decimal digits.
Specifically, $x$ is the digit at the $10^{10}$ place (the eleventh digit from the right, $d_{10}$) and
$y$ is the digit at the $10^5$ place (the sixth digit from the right, $d_5$).
Find the values of $x$ and $y$. Show that $x=0$ and $y=6$. -/

theorem number_theory_636482 (N_0 x y: ℕ) (h1: N_0 = 20) (h2: x = ((Nat.factorial N_0) / 10 ^ 10) % 10)
  (h3: y = ((Nat.factorial N_0) / 10 ^ 5) % 10): x = 0 ∧ y = 6 := by

  simp [h1, h2, h3]
  native_decide