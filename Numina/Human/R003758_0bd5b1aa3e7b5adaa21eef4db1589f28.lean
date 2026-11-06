import Mathlib

def f (k : ℕ) := (Nat.digits 10 k).sum ^ 2

/- Example 2 The square of the sum of the digits of a natural number $k$ is denoted as $f_{1}(k)$, and $f_{n}(k)=f_{1}\left[f_{n-1}(k)\right]$, then the range of $f_{n}(11)(n \in$ $\left.\mathbf{N}^{*}\right)$ is
A. $\mathbf{N}^{*}$
B. 5
C. $\{4,16,49,169,256\}$
D. $\{2,4,7,13,16\}$ -/
theorem number_theory_211411: 
  {x | ∃ n : ℕ, 1 ≤ n ∧ (f^[n] 11) = x} = {x | x= 4 ∨ x =16 ∨ x=49 ∨ x=169 ∨ x=256} := by
  ext x
  simp

  constructor

  intro h
  obtain ⟨n, nge1, hn⟩ := h
  have lem : ∀m : ℕ ,f^[m+1] 11 = 4 ∨ f^[m+1] 11 = 16 ∨ f^[m+1] 11 = 49 ∨ f^[m+1] 11 = 169 ∨ f^[m+1] 11 = 256 := by 
    intro m
    induction' m with m hn
    simp [f]

    have : (f^[m + 1 + 1] 11) = f ((f^[m+1]) 11) := by exact Function.iterate_succ_apply' f (m + 1) 11
    rw [this];

    rcases hn with hn | hn | hn | hn | hn
    
    right;left; 
    rw [hn]; 
    simp [f]

    right;right;left;
    rw [hn];
    simp [f]

    right;right;right;left
    rw [hn];
    simp [f]

    right;right;right;right
    rw [hn]
    simp [f]

    right;right;right;left
    rw [hn]
    simp [f]
    

  rw [←hn];
  have exi : ∃ k : ℕ, k+1 = n := by use n-1; omega
  obtain ⟨k,hk⟩ := exi
  have : f^[k + 1] 11 = 4 ∨ f^[k + 1] 11 = 16 ∨ f^[k + 1] 11 = 49 ∨ f^[k + 1] 11 = 169 ∨ f^[k + 1] 11 = 256 := by apply lem k
  rw [hk] at this
  assumption

  intro h
  rcases h with h | h | h | h | h
  use 1; simp [f,h];
  use 2; simp [f,h];
  use 3; simp [f,h];
  use 4; simp [f,h];
  use 5; simp [f,h];