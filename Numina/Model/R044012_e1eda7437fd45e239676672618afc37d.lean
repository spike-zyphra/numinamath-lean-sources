import Mathlib

/- The function $\varphi(x,y,z)$ defined for all triples $(x,y,z)$ of real numbers, is such that
there are two functions $f$ and $g$ defined for all pairs of real numbers, such that
\[\varphi(x,y,z) = f(x+y,z) = g(x,y+z)\]
for all real numbers $x,y$ and $z.$ Show that there is a function $h$ of one real variable,
such that \[\varphi(x,y,z) = h(x+y+z)\] for all real numbers $x,y$ and $z.$ -/

-- Define a theorem named algebra_85123 that takes a function φ mapping three real numbers to a real number
theorem algebra_85123 (φ : ℝ → ℝ → ℝ → ℝ)
    -- Given the existence of two functions f and g, each taking two real numbers,
    -- such that φ(x,y,z) equals both f(x+y,z) and g(x,y+z) for all x, y, z
    (hfg : ∃ f g : ℝ → ℝ → ℝ,
      ∀ x y z, φ x y z = f (x + y) z ∧ φ x y z = g x (y + z)) :
    -- Prove there exists a function h of one real variable such that φ(x,y,z) = h(x+y+z)
    ∃ h : ℝ → ℝ, ∀ x y z, φ x y z = h (x + y + z) := by
  rcases hfg with ⟨f, g, hfg⟩
  have eq1 : ∀ x y z, f (x + y) z = g x (y + z) := by
    intro x y z
    have h1 := (hfg x y z).1
    have h2 := (hfg x y z).2
    linarith
  use fun w => g 0 w
  intro x y z
  have eq2 : φ x y z = f (x + y) z := by
    have h1 := (hfg x y z).1
    linarith
  have eq4 : f (x + y) z = g 0 (x + y + z) := by
    have eq5 : f (x + y) z = g 0 ((x + y) + z) := by
      specialize eq1 0 (x + y) z
      norm_num at eq1
      all_goals
        try { 
          ring_nf at eq1 ⊢
          all_goals linarith
        }
    ring_nf at eq5 ⊢
    all_goals linarith
  calc
    φ x y z = f (x + y) z := by linarith [eq2]
    _ = g 0 (x + y + z) := by linarith [eq4]
    _ = (fun w => g 0 w) (x + y + z) := by 
      simp