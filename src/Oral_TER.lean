import analysis.complex.basic 
import analysis.calculus.deriv

noncomputable theory

example (a b c : ℝ) (hc : 0 ≤ c) (hab : a ≤ b) : a * c ≤ b * c := 
begin
rw ← sub_nonneg,
have h_fact : b * c - a * c = (b - a) * c, { ring },
rw h_fact,
apply mul_nonneg,
{ rw sub_nonneg,
    exact hab },
  { exact hc },
end
