theory T1_2025_1
  imports Main
begin

primrec pot :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
poteq1: "pot x 0 = Suc 0" |
poteq2: "pot x (Suc y) = x * pot x y"

(* Lema: pot(x, m + n) = pot(x, m) * pot(x, n) *)
lemma t1: "\<forall>x m::nat. pot x (m + n) = pot x m * pot x n"
proof (induction n)
  case 0
  show "\<forall>x m::nat. pot x (m + 0) = pot x m * pot x 0"
  proof (rule allI, rule allI)
    fix A :: nat and B :: nat
    have "pot A (B + 0) = pot A B" by simp
    also have "... = pot A B * 1" by simp
    also have "... = pot A B * pot A 0" by (simp only: poteq1)
    finally show "pot A (B + 0) = pot A B * pot A 0" .
  qed
next
  case (Suc n)
  show "\<forall>x m::nat. pot x (m + Suc n) = pot x m * pot x (Suc n)"
  (*Suc.IH: \<forall>x m. pot x (m + n) = pot x m * pot x n*)
  proof (rule allI, rule allI)
    fix A :: nat and B :: nat
    have "pot A (B + Suc n) = pot A (Suc (B + n))" by simp
    also have "... = A * pot A (B + n)" by (simp only: poteq2)
    also have "... = A * (pot A B * pot A n)" using Suc.IH by simp
    also have "... = (A * pot A n) * pot A B" by simp
    also have "... = pot A (Suc n) * pot A B" by (simp only: poteq2)
    also have "... = pot A B * pot A (Suc n)" by simp
    finally show "pot A (B + Suc n) = pot A B * pot A (Suc n)" .
  qed
qed

(* Teorema: pot(x, m * n) = pot(pot(x, m), n) *)
theorem t2: "\<forall>x m::nat. pot x (m * n) = pot (pot x m) n"
  sorry

primrec cat :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
cateq1: "cat [] ys = ys" |
cateq2: "cat (x#xs) ys = x#cat xs ys"

primrec reverso :: "'a list \<Rightarrow> 'a list" where
reveq1: "reverso [] = []" |
reveq2: "reverso (x#xs) = cat (reverso xs) [x]"

primrec somatorio :: "nat list \<Rightarrow> nat" where
somaeq1: "somatorio [] = 0" |
somaeq2: "somatorio (x#xs) = x + somatorio xs"

lemma t3: "\<forall>ys::nat list. somatorio (cat xs ys) = somatorio xs + somatorio ys"
  sorry

theorem t4: "somatorio (reverso xs) = somatorio xs"
  sorry

end