module Изоморфизм_Карри-Говарда where

{- Часть 3 | Изоморфизм Карри - Говарда. -}

open import Вспомогательные_определения
open import Интуиционистское_Исчисление_Высказываний
open import Просто_типизированное_лямбда_исчисление

{-
Другое название изоморфизма К-Г - Propositions as Types.
Сейчас мы устроим отображения между высказываниями и типами в обе стороны.
-}

Π→Φ : Π → Φ
Π→Φ (тпер x) = ппер x
Π→Φ (φ ⇒ ψ) = (Π→Φ φ) ⊃ (Π→Φ ψ)

Φ→Π : Φ → Π
Φ→Π (ппер x) = тпер x
Φ→Π (φ ⊃ ψ) = (Φ→Π φ) ⇒ (Φ→Π ψ)

{-
Следующая теорема доказывает что наши 2 отображения действительно
образуют изоморфизм.
Теорема. Пусть φ - произвольная формула ПФ ИИВ, τ - произвольный простой тип.
         Тогда
         (i) fromΠ (toΠ φ) ≡ φ
         (ii) toΠ (fromΠ τ) ≡ τ
Доказательство. Индукцией по структуре формулы и структуре типа соответственно ∎
-}

Φ→Π→Φ : ∀{φ} → Π→Φ  (Φ→Π φ) ≡ φ
Φ→Π→Φ {ппер x} = рефл
Φ→Π→Φ {φ ⊃ ψ} rewrite Φ→Π→Φ {φ} | Φ→Π→Φ {ψ} = рефл

Π→Φ→Π : ∀{τ} → Φ→Π (Π→Φ τ) ≡ τ
Π→Φ→Π {тпер x} = рефл
Π→Φ→Π {τ ⇒ σ} rewrite Π→Φ→Π {τ} | Π→Φ→Π {σ} = рефл

{- Прежде чем сделать следующий шаг и доказать собственно изоморфизм
Карри-Говарда между доказательсвами и типизируемыми термами,
нам необходимо провести небольшую подготовительную работу и
навести изоморфизм между контекстами -}

{- В одну сторону (связки → формулы) - тривиально, просто отсекаем переменные -}

∣_∣ : Список Связка → Список Φ
∣ Γ ∣ = отобразить Π→Φ на (область_значения Γ)

{- В обратную сторону немного сложнее. Каждой формуле поставим в соответствие
связку x_φ : (toΠ φ), где х - переменная, имя которой зависит от φ.
Так как переменные у нас - строки, нужно будет также сделать
функцию showΦ : Φ → String -}

_встроку : Φ → Строка
(ппер x) встроку = x
(φ ⊃ ψ) встроку = ψ встроку конкатенировать " -> " конкатенировать ψ встроку

сделать_Δ_из : Список Φ → Список Связка
сделать_Δ_из формулы =
  отобразить (λ φ → ("x_" конкатенировать φ встроку) типа Φ→Π φ) на формулы

{-
Теперь все готово к финальному доказательству.

Теорема (Изоморфизм Карри - Говарда).
  (i)  Если Γ ⊢ M : φ, то ran(Γ) ⊢ φ
  (ii) Если Γ ‌⊢ φ, то  ∃ M ∈ Λ . Δ ⊢ M : φ, где Δ = [(x_φ : φ) | φ ∈ Γ].
Доказательство. Индукцией по выводу Γ ⊢ M : φ и Γ ⊢ φ соответственно. ∎
-}

Изоморфизм_Карри-Говарда-i : ∀{Γ M φ} →
  Γ ⊢ M ∶ φ → ∣ Γ ∣ ⊢ Π→Φ φ
Изоморфизм_Карри-Говарда-i Аксиома = Аксиома
Изоморфизм_Карри-Говарда-i (Абстрагировать p) =
  ⊃В (Изоморфизм_Карри-Говарда-i p)
Изоморфизм_Карри-Говарда-i (Применить M к N) =
  ⊃У (Изоморфизм_Карри-Говарда-i M) (Изоморфизм_Карри-Говарда-i N)

Изоморфизм_Карри-Говарда-ii : ∀ {Γ φ} →
  Γ ⊢ φ → ∃[ M ∈ Λ ] сделать_Δ_из Γ ⊢ M ∶ Φ→Π φ
Изоморфизм_Карри-Говарда-ii Аксиома = _ , Аксиома
Изоморфизм_Карри-Говарда-ii (⊃В {φ = φ} p) =
  ƛ x ! пр₁ p' , Абстрагировать (пр₂ p')
  where
    p' = Изоморфизм_Карри-Говарда-ii p
    x = "x_" конкатенировать φ встроку
Изоморфизм_Карри-Говарда-ii (⊃У p q) =
  пр₁ p' $ пр₁ q' , (Применить (пр₂ p') к (пр₂ q'))
  where
    p' = Изоморфизм_Карри-Говарда-ii p
    q' = Изоморфизм_Карри-Говарда-ii q
