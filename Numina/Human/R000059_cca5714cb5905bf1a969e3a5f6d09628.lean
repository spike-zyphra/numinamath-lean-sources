import Mathlib

/- recurrence pattern : 1, 1, -1, -1, -1, 1, -1 -/
def pat (n : ℕ) : ℤ := match n % 7 with
  | 0  => 1
  | 1 => 1
  | 2 => -1
  | 3 => -1
  | 4 => -1
  | 5 => 1
  | 6 => -1
  | _ => 0 -- never

/- pat(n) = pat(n%7) -/
lemma aux_4195 (n : ℕ) : pat n = pat (n % 7) := by simp [pat]

/- For the infinite sequence of numbers \( x_{1}, x_{2}, x_{3}, \ldots \), the relationship \( x_{n} = x_{n-1} \cdot x_{n-3} \) holds for all natural numbers \( n \geq 4 \). It is known that \( x_{1} = 1 \), \( x_{2} = 1 \), and \( x_{3} = -1 \). Find \( x_{2022} \).-/
theorem recurrence_relations_4195 {x : ℕ → ℤ} (h0 : x 0 = 1) (h1 : x 1 = 1) (h2 : x 2 = -1)
    (hn : ∀ n, x (n + 3) = x (n + 2) * x n) : x 2021 = 1 := by
  have hp n : x n = pat n := by
    -- using second mathematical induction
    induction' n using Nat.strongRecOn with n ih
    -- check n=0,1,2 satisfy requirement
    iterate 3 cases' n with n; simpa [pat]
    -- use x(n+3) = x(n+2) * x(n)
    rw [show n + 1 + 1 + 1 = n + 3 by ring, hn n]
    -- use induction hypothesis
    rw [ih (n + 2) (by linarith), ih n (by linarith)]
    rw [aux_4195 (n + 2), aux_4195 n, aux_4195 (n + 3)]
    rw [Nat.add_mod, Nat.add_mod n 3]
    -- suffices to check n%7=0,1,2,3,4,5,6
    have : n % 7 < 7 := by apply Nat.mod_lt; norm_num
    interval_cases n % 7 <;> simp [pat]
  -- substitude n=2021 to hp gives the desired conclusion
  simp [hp 2021, pat]
