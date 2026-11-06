import Mathlib

/- Recall that if $b$ is a residue $\pmod{m}$, then the modular inverse of $b$ is the residue $c$ for which $bc \equiv 1\pmod{m}$. The table below shows the inverses of the first 9 positive residues modulo 47.  \begin{tabular}{c|ccccccccc}
$b$ & 1 & 2 & 3 & 4 & 5 & 6 & 7 & 8 & 9 \\ \hline
inverse of $\,b$ & 1 & 24 & 16 & 12 & 19 & 8 & 27 & 6 & 21
\end{tabular}Find the modular inverse of $35\pmod{47}$.

Express your answer as an integer from $0$ to $46$, inclusive. -/
theorem number_theory_19026 {n : ℕ} (hn : 35 * n ≡ 1 [MOD 47]) (hn₁ : n ≤ 46) :  n = 43 := by 
  rw [Nat.ModEq] at hn
  omega