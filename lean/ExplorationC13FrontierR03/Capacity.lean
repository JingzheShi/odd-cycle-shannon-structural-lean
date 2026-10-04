import ExplorationC13FrontierR03.TypedTables
import ExplorationC13FrontierR03.PublicLongCapacity
import ShannonBounds.Reindex

set_option maxRecDepth 4000000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 4000
set_option exponentiation.threshold 20000

namespace ShannonBounds.ExplorationC13FrontierR03.Capacity
open SimpleGraph TypeModel TypedTables

def N : Nat := 2296588622609241065952539522720457225166668490849988910030745659472084374777779848432674982577570275992208029871641156373956233997378729690521765852128859668435944150723661063476206335279190203088236542001430889013443359535528680189396857994367355610053164914628938826966334878872556863600355375516196718498778074573416772206444694488798046323348177694719494878137521970969100483646258158547494769299673652709061296128

def flipIndex (letter : Ty) : Ty :=
  match letter.val with
  | 0 => 0
  | 1 => 1
  | 2 => 4
  | 3 => 5
  | 4 => 2
  | 5 => 3
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | 9 => 9
  | 10 => 18
  | 11 => 19
  | 12 => 20
  | 13 => 21
  | 14 => 22
  | 15 => 23
  | 16 => 24
  | 17 => 25
  | 18 => 10
  | 19 => 11
  | 20 => 12
  | 21 => 13
  | 22 => 14
  | 23 => 15
  | 24 => 16
  | 25 => 17
  | 26 => 26
  | 27 => 28
  | 28 => 27
  | 29 => 29
  | 30 => 34
  | 31 => 36
  | 32 => 35
  | 33 => 37
  | 34 => 30
  | 35 => 32
  | 36 => 31
  | 37 => 33
  | 38 => 38
  | 39 => 40
  | 40 => 39
  | 41 => 41
  | 42 => 50
  | 43 => 51
  | 44 => 52
  | 45 => 53
  | 46 => 54
  | 47 => 55
  | 48 => 56
  | 49 => 57
  | 50 => 42
  | 51 => 43
  | 52 => 44
  | 53 => 45
  | 54 => 46
  | 55 => 47
  | 56 => 48
  | 57 => 49
  | _ => 0

def typedFlip : Ty ≃ Ty where
  toFun := flipIndex
  invFun := flipIndex
  left_inv := by native_decide
  right_inv := by native_decide

theorem flip_sep : ∀ first second, typedSep (typedFlip first) (typedFlip second) = typedSep first second := by native_decide

section Generic
variable {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
  {graph : SimpleGraph Vertex} [DecidableRel graph.Adj]

def R_R1 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 1) :=
  base.mapIso (strongPower_one_iso graph).symm

def w_R1 : Ty → Nat := TypedBase.w0

theorem step_R1 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_R1 base).w letter = w_R1 letter := by
  rw [R_R1, Realisation.w_mapIso]
  exact correct letter

def R_Rf (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 1) :=
  (R_R1 base).reindex typedFlip flip_sep

def w_Rf (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 58136
  | 3 => 1521
  | 5 => 1859
  | 9 => 60502
  | 15 => 1014
  | 25 => 1014
  | 40 => 1014
  | 49 => 1014
  | 57 => 1014
  | _ => 0

theorem flip_weights : ∀ letter, TypedBase.w0 (typedFlip letter) = w_Rf letter := by native_decide

theorem step_Rf (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_Rf base).w letter = w_Rf letter := by
  change (R_R1 base).w (typedFlip letter) = w_Rf letter
  rw [step_R1 base correct]
  exact flip_weights letter

def e_n0 : Fin 3 → Nat := Fin.cases (1) (Fin.cases (1) (fun _ => 1))

def children_n0 (base : Realisation Ty typedSep graph) :
    (index : Fin 3) → Realisation Ty typedSep (strongPower graph (e_n0 index)) :=
  Fin.cases (R_Rf base) (Fin.cases (R_Rf base) (fun _ => R_R1 base))

def R_n0 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 3) :=
  Realisation.multiSubst e_n0 (children_n0 base) S_n0

def w_n0 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 196615276420472
  | 2 => 183322205820
  | 3 => 17103696328511
  | 5 => 18241674471969
  | 7 => 1028631612372
  | 9 => 221663094285880
  | 15 => 11696130496440
  | 23 => 11135216676168
  | 47 => 11321840419344
  | 55 => 11508464162520
  | _ => 0

theorem polynomial_n0 : ∀ letter, (∑ word ∈ S_n0.T letter, w_Rf (word 0) * w_Rf (word 1) * w_R1 (word 2)) = w_n0 letter := by native_decide

theorem step_n0 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n0 base).w letter = w_n0 letter := by
  change (Realisation.multiSubst e_n0 (children_n0 base) S_n0).w letter = w_n0 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n0 base 0).w value = w_Rf value := fun value => step_Rf base correct value
  have child1 : ∀ value, (children_n0 base 1).w value = w_Rf value := fun value => step_Rf base correct value
  have child2 : ∀ value, (children_n0 base 2).w value = w_R1 value := fun value => step_R1 base correct value
  simp only [Fin.prod_univ_three, child0, child1, child2]
  exact polynomial_n0 letter

def e_n1 : Fin 3 → Nat := Fin.cases (1) (Fin.cases (3) (fun _ => 1))

def children_n1 (base : Realisation Ty typedSep graph) :
    (index : Fin 3) → Realisation Ty typedSep (strongPower graph (e_n1 index)) :=
  Fin.cases (R_R1 base) (Fin.cases (R_n0 base) (fun _ => R_Rf base))

def R_n1 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 5) :=
  Realisation.multiSubst e_n1 (children_n1 base) S_n1

def w_n1 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 665477607478594457160848
  | 2 => 2261547260748722264292
  | 3 => 101244034065565905704385
  | 5 => 104479949482394365134203
  | 7 => 12276116657566397362896
  | 9 => 813141952706424045459040
  | 11 => 11246639137872942960
  | 15 => 74897527463120023081680
  | 23 => 67958002361742605609952
  | 46 => 11246639137872942960
  | 47 => 70258484506119443929200
  | 55 => 72581395966843281937536
  | _ => 0

theorem polynomial_n1 : ∀ letter, (∑ word ∈ S_n1.T letter, w_R1 (word 0) * w_n0 (word 1) * w_Rf (word 2)) = w_n1 letter := by native_decide

theorem step_n1 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n1 base).w letter = w_n1 letter := by
  change (Realisation.multiSubst e_n1 (children_n1 base) S_n1).w letter = w_n1 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n1 base 0).w value = w_R1 value := fun value => step_R1 base correct value
  have child1 : ∀ value, (children_n1 base 1).w value = w_n0 value := fun value => step_n0 base correct value
  have child2 : ∀ value, (children_n1 base 2).w value = w_Rf value := fun value => step_Rf base correct value
  simp only [Fin.prod_univ_three, child0, child1, child2]
  exact polynomial_n1 letter

def e_n2 : Fin 2 → Nat := Fin.cases (5) (fun _ => 1)

def children_n2 (base : Realisation Ty typedSep graph) :
    (index : Fin 2) → Realisation Ty typedSep (strongPower graph (e_n2 index)) :=
  Fin.cases (R_n1 base) (fun _ => R_Rf base)

def R_n2 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 6) :=
  Realisation.multiSubst e_n2 (children_n2 base) S_n2

def w_n2 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 38688217592467653164667220768
  | 2 => 204590942303426594334689868
  | 3 => 7390644602297536118565406159
  | 5 => 7245151787246142810152798179
  | 7 => 1103397994208351367536763298
  | 9 => 49272671919583757104931823040
  | 11 => 2973653083518793170958008
  | 15 => 5569803552070572547578360840
  | 23 => 4936120998934465106708782464
  | 46 => 691848253205391959127360
  | 47 => 5146546872922757694844133760
  | 54 => 11404092085803164161440
  | 55 => 5360685197629850429909139936
  | _ => 0

theorem polynomial_n2 : ∀ letter, (∑ word ∈ S_n2.T letter, w_n1 (word 0) * w_Rf (word 1)) = w_n2 letter := by native_decide

theorem step_n2 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n2 base).w letter = w_n2 letter := by
  change (Realisation.multiSubst e_n2 (children_n2 base) S_n2).w letter = w_n2 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n2 base 0).w value = w_n1 value := fun value => step_n1 base correct value
  have child1 : ∀ value, (children_n2 base 1).w value = w_Rf value := fun value => step_Rf base correct value
  simp only [Fin.prod_univ_two, child0, child1]
  exact polynomial_n2 letter

def e_n3 : Fin 2 → Nat := Fin.cases (6) (fun _ => 1)

def children_n3 (base : Realisation Ty typedSep graph) :
    (index : Fin 2) → Realisation Ty typedSep (strongPower graph (e_n3 index)) :=
  Fin.cases (R_n2 base) (fun _ => R_R1 base)

def R_n3 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 7) :=
  Realisation.multiSubst e_n3 (children_n3 base) S_n3

def w_n3 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 2249181233239926172437368897988560
  | 2 => 17210508537915067956427298873772
  | 3 => 505776579360949043290827924371963
  | 5 => 506594277980229705128233490156817
  | 7 => 92635715195793445584047027119608
  | 9 => 2986745992564682720982104966877952
  | 11 => 387367174354728591084676926168
  | 14 => 11563749375004408459700160
  | 15 => 402614611734576755257091659896936
  | 23 => 348607682003990937590495625199488
  | 46 => 42559737144182891757678677760
  | 47 => 366557466761174292060432600942720
  | 54 => 1391504508125530484650585920
  | 55 => 384949010036748860057671932198336
  | _ => 0

theorem polynomial_n3 : ∀ letter, (∑ word ∈ S_n3.T letter, w_n2 (word 0) * w_R1 (word 1)) = w_n3 letter := by native_decide

theorem step_n3 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n3 base).w letter = w_n3 letter := by
  change (Realisation.multiSubst e_n3 (children_n3 base) S_n3).w letter = w_n3 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n3 base 0).w value = w_n2 value := fun value => step_n2 base correct value
  have child1 : ∀ value, (children_n3 base 1).w value = w_R1 value := fun value => step_R1 base correct value
  simp only [Fin.prod_univ_two, child0, child1]
  exact polynomial_n3 letter

def e_n4 : Fin 2 → Nat := Fin.cases (7) (fun _ => 1)

def children_n4 (base : Realisation Ty typedSep graph) :
    (index : Fin 2) → Realisation Ty typedSep (strongPower graph (e_n4 index)) :=
  Fin.cases (R_n3 base) (fun _ => R_R1 base)

def R_n4 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 8) :=
  Realisation.multiSubst e_n4 (children_n4 base) S_n4

def w_n4 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 130758792965951143655610238115866058512
  | 2 => 1380215497398446019793345932864897036
  | 3 => 34034363614090551591294319047976593943
  | 5 => 34574351620016903913729437023318968955
  | 7 => 7409347213824363251525929170225803602
  | 9 => 181112750060487732375735835689724441600
  | 11 => 40887944440255668125622404445021144
  | 14 => 2110615535925804632064473203200
  | 15 => 28503962159952447944950445532677680680
  | 23 => 24120022413066047985176020752233666304
  | 46 => 2618104790161554769365361541084160
  | 47 => 25577709561740986029465426316006606848
  | 54 => 127344379214812297624615928580480
  | 55 => 27080774420162633125820791110577121664
  | _ => 0

theorem polynomial_n4 : ∀ letter, (∑ word ∈ S_n4.T letter, w_n3 (word 0) * w_R1 (word 1)) = w_n4 letter := by native_decide

theorem step_n4 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n4 base).w letter = w_n4 letter := by
  change (Realisation.multiSubst e_n4 (children_n4 base) S_n4).w letter = w_n4 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n4 base 0).w value = w_n3 value := fun value => step_n3 base correct value
  have child1 : ∀ value, (children_n4 base 1).w value = w_R1 value := fun value => step_R1 base correct value
  simp only [Fin.prod_univ_two, child0, child1]
  exact polynomial_n4 letter

def e_n5 : Fin 2 → Nat := Fin.cases (8) (fun _ => 1)

def children_n5 (base : Realisation Ty typedSep graph) :
    (index : Fin 2) → Realisation Ty typedSep (strongPower graph (e_n5 index)) :=
  Fin.cases (R_n4 base) (fun _ => R_R1 base)

def R_n5 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 9) :=
  Realisation.multiSubst e_n5 (children_n5 base) S_n5

def w_n5 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 7601834648244198106810036184222096429093648
  | 2 => 106797218655148066859780123359686100108908
  | 3 => 2260740994607031372577769842392078779698547
  | 5 => 2317368821566617326359977006871416545229033
  | 7 => 571650873978259576041867671658267174301224
  | 9 => 10986628084305647139089194560701326413377536
  | 11 => 3873340928886372697006859489657674848792
  | 14 => 256823661678402701640525309320613120
  | 15 => 1986136057980014212097872785131346024463080
  | 23 => 1642957924596656595828115744941021862507008
  | 46 => 161055334271578203192279580561333186560
  | 47 => 1757086709961393057217591302644843010643968
  | 54 => 10359347888478390167020989513635539200
  | 55 => 1875485174414864983650535656992625080015616
  | _ => 0

theorem polynomial_n5 : ∀ letter, (∑ word ∈ S_n5.T letter, w_n4 (word 0) * w_R1 (word 1)) = w_n5 letter := by native_decide

theorem step_n5 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n5 base).w letter = w_n5 letter := by
  change (Realisation.multiSubst e_n5 (children_n5 base) S_n5).w letter = w_n5 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n5 base 0).w value = w_n4 value := fun value => step_n4 base correct value
  have child1 : ∀ value, (children_n5 base 1).w value = w_R1 value := fun value => step_R1 base correct value
  simp only [Fin.prod_univ_two, child0, child1]
  exact polynomial_n5 letter

def e_n6 : Fin 3 → Nat := Fin.cases (1) (Fin.cases (1) (fun _ => 1))

def children_n6 (base : Realisation Ty typedSep graph) :
    (index : Fin 3) → Realisation Ty typedSep (strongPower graph (e_n6 index)) :=
  Fin.cases (R_R1 base) (Fin.cases (R_R1 base) (fun _ => R_R1 base))

def R_n6 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 3) :=
  Realisation.multiSubst e_n6 (children_n6 base) S_n6

def w_n6 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 196615276420472
  | 2 => 183322205820
  | 3 => 19530036676631
  | 5 => 15829003646937
  | 7 => 1014962089284
  | 9 => 221663094285880
  | 15 => 11696130496440
  | 23 => 11135216676168
  | 47 => 11321840419344
  | 55 => 11508464162520
  | _ => 0

theorem polynomial_n6 : ∀ letter, (∑ word ∈ S_n6.T letter, w_R1 (word 0) * w_R1 (word 1) * w_R1 (word 2)) = w_n6 letter := by native_decide

theorem step_n6 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n6 base).w letter = w_n6 letter := by
  change (Realisation.multiSubst e_n6 (children_n6 base) S_n6).w letter = w_n6 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n6 base 0).w value = w_R1 value := fun value => step_R1 base correct value
  have child1 : ∀ value, (children_n6 base 1).w value = w_R1 value := fun value => step_R1 base correct value
  have child2 : ∀ value, (children_n6 base 2).w value = w_R1 value := fun value => step_R1 base correct value
  simp only [Fin.prod_univ_three, child0, child1, child2]
  exact polynomial_n6 letter

def e_n7 : Fin 3 → Nat := Fin.cases (1) (Fin.cases (1) (fun _ => 1))

def children_n7 (base : Realisation Ty typedSep graph) :
    (index : Fin 3) → Realisation Ty typedSep (strongPower graph (e_n7 index)) :=
  Fin.cases (R_Rf base) (Fin.cases (R_R1 base) (fun _ => R_Rf base))

def R_n7 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 3) :=
  Realisation.multiSubst e_n7 (children_n7 base) S_n7

def w_n7 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 196615276420472
  | 2 => 183669736068
  | 3 => 17103348798263
  | 5 => 18241674471969
  | 7 => 1028631612372
  | 9 => 221663094285880
  | 15 => 11696130496440
  | 23 => 11135216676168
  | 47 => 11321840419344
  | 55 => 11508464162520
  | _ => 0

theorem polynomial_n7 : ∀ letter, (∑ word ∈ S_n7.T letter, w_Rf (word 0) * w_R1 (word 1) * w_Rf (word 2)) = w_n7 letter := by native_decide

theorem step_n7 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n7 base).w letter = w_n7 letter := by
  change (Realisation.multiSubst e_n7 (children_n7 base) S_n7).w letter = w_n7 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n7 base 0).w value = w_Rf value := fun value => step_Rf base correct value
  have child1 : ∀ value, (children_n7 base 1).w value = w_R1 value := fun value => step_R1 base correct value
  have child2 : ∀ value, (children_n7 base 2).w value = w_Rf value := fun value => step_Rf base correct value
  simp only [Fin.prod_univ_three, child0, child1, child2]
  exact polynomial_n7 letter

def e_n8 : Fin 3 → Nat := Fin.cases (1) (Fin.cases (3) (fun _ => 1))

def children_n8 (base : Realisation Ty typedSep graph) :
    (index : Fin 3) → Realisation Ty typedSep (strongPower graph (e_n8 index)) :=
  Fin.cases (R_Rf base) (Fin.cases (R_n7 base) (fun _ => R_R1 base))

def R_n8 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 5) :=
  Realisation.multiSubst e_n8 (children_n8 base) S_n8

def w_n8 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 665477607835923668033456
  | 2 => 2255403173558184619164
  | 3 => 101250249072678990149073
  | 5 => 104479949482394365134203
  | 7 => 12276045380314639690728
  | 9 => 813141952706424045459040
  | 11 => 11267959780788341904
  | 15 => 74897506142477107682736
  | 23 => 67958002361742605609952
  | 46 => 11267959780788341904
  | 47 => 70258463185476528530256
  | 55 => 72581395966843281937536
  | _ => 0

theorem polynomial_n8 : ∀ letter, (∑ word ∈ S_n8.T letter, w_Rf (word 0) * w_n7 (word 1) * w_R1 (word 2)) = w_n8 letter := by native_decide

theorem step_n8 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n8 base).w letter = w_n8 letter := by
  change (Realisation.multiSubst e_n8 (children_n8 base) S_n8).w letter = w_n8 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n8 base 0).w value = w_Rf value := fun value => step_Rf base correct value
  have child1 : ∀ value, (children_n8 base 1).w value = w_n7 value := fun value => step_n7 base correct value
  have child2 : ∀ value, (children_n8 base 2).w value = w_R1 value := fun value => step_R1 base correct value
  simp only [Fin.prod_univ_three, child0, child1, child2]
  exact polynomial_n8 letter

def e_n9 : Fin 2 → Nat := Fin.cases (5) (fun _ => 1)

def children_n9 (base : Realisation Ty typedSep graph) :
    (index : Fin 2) → Realisation Ty typedSep (strongPower graph (e_n9 index)) :=
  Fin.cases (R_n8 base) (fun _ => R_Rf base)

def R_n9 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 6) :=
  Realisation.multiSubst e_n9 (children_n9 base) S_n9

def w_n9 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 38688217634860476084171688672
  | 2 => 204222327792430288315235508
  | 3 => 7391008105537811898863872087
  | 5 => 7245151787789640539890034947
  | 7 => 1103403062542751244016047058
  | 9 => 49272671919583757104931823040
  | 11 => 2968712920645255465708104
  | 15 => 5569808492233446085283610744
  | 23 => 4936120998934465106708782464
  | 46 => 693159813874975640566464
  | 47 => 5146545561362088111162694656
  | 54 => 11425711217719378690656
  | 55 => 5360685176010718513694610720
  | _ => 0

theorem polynomial_n9 : ∀ letter, (∑ word ∈ S_n9.T letter, w_n8 (word 0) * w_Rf (word 1)) = w_n9 letter := by native_decide

theorem step_n9 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n9 base).w letter = w_n9 letter := by
  change (Realisation.multiSubst e_n9 (children_n9 base) S_n9).w letter = w_n9 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n9 base 0).w value = w_n8 value := fun value => step_n8 base correct value
  have child1 : ∀ value, (children_n9 base 1).w value = w_Rf value := fun value => step_Rf base correct value
  simp only [Fin.prod_univ_two, child0, child1]
  exact polynomial_n9 letter

def e_n10 : Fin 2 → Nat := Fin.cases (6) (fun _ => 1)

def children_n10 (base : Realisation Ty typedSep graph) :
    (index : Fin 2) → Realisation Ty typedSep (strongPower graph (e_n10 index)) :=
  Fin.cases (R_n9 base) (fun _ => R_R1 base)

def R_n10 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 7) :=
  Realisation.multiSubst e_n10 (children_n10 base) S_n10

def w_n10 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 2249181230695150171918447520652848
  | 2 => 17188518102032561328224710119252
  | 3 => 505797584693182870811002759668059
  | 5 => 506594278091645109231177815886513
  | 7 => 92636702732802721108051832184048
  | 9 => 2986745992564682720982104966877952
  | 11 => 386694509506403558537920513320
  | 14 => 11585671174767449992325184
  | 15 => 402615284377503280526596883684760
  | 23 => 348607682003990937590495625199488
  | 46 => 42640419110333001505086599424
  | 47 => 366557386079208141950685193021056
  | 54 => 1394142431363683149076463808
  | 55 => 384949007398825621905007506320448
  | _ => 0

theorem polynomial_n10 : ∀ letter, (∑ word ∈ S_n10.T letter, w_n9 (word 0) * w_R1 (word 1)) = w_n10 letter := by native_decide

theorem step_n10 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n10 base).w letter = w_n10 letter := by
  change (Realisation.multiSubst e_n10 (children_n10 base) S_n10).w letter = w_n10 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n10 base 0).w value = w_n9 value := fun value => step_n9 base correct value
  have child1 : ∀ value, (children_n10 base 1).w value = w_R1 value := fun value => step_R1 base correct value
  simp only [Fin.prod_univ_two, child0, child1]
  exact polynomial_n10 letter

def e_n11 : Fin 3 → Nat := Fin.cases (1) (Fin.cases (1) (fun _ => 1))

def children_n11 (base : Realisation Ty typedSep graph) :
    (index : Fin 3) → Realisation Ty typedSep (strongPower graph (e_n11 index)) :=
  Fin.cases (R_R1 base) (Fin.cases (R_R1 base) (fun _ => R_Rf base))

def R_n11 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 3) :=
  Realisation.multiSubst e_n11 (children_n11 base) S_n11

def w_n11 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 196615276420472
  | 2 => 183669736068
  | 3 => 18313091937933
  | 5 => 17031931332299
  | 7 => 1028631612372
  | 9 => 221663094285880
  | 15 => 11696130496440
  | 23 => 11135216676168
  | 47 => 11321840419344
  | 55 => 11508464162520
  | _ => 0

theorem polynomial_n11 : ∀ letter, (∑ word ∈ S_n11.T letter, w_R1 (word 0) * w_R1 (word 1) * w_Rf (word 2)) = w_n11 letter := by native_decide

theorem step_n11 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n11 base).w letter = w_n11 letter := by
  change (Realisation.multiSubst e_n11 (children_n11 base) S_n11).w letter = w_n11 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n11 base 0).w value = w_R1 value := fun value => step_R1 base correct value
  have child1 : ∀ value, (children_n11 base 1).w value = w_R1 value := fun value => step_R1 base correct value
  have child2 : ∀ value, (children_n11 base 2).w value = w_Rf value := fun value => step_Rf base correct value
  simp only [Fin.prod_univ_three, child0, child1, child2]
  exact polynomial_n11 letter

def e_n12 : Fin 3 → Nat := Fin.cases (3) (Fin.cases (7) (fun _ => 3))

def children_n12 (base : Realisation Ty typedSep graph) :
    (index : Fin 3) → Realisation Ty typedSep (strongPower graph (e_n12 index)) :=
  Fin.cases (R_n6 base) (Fin.cases (R_n10 base) (fun _ => R_n11 base))

def R_n12 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 13) :=
  Realisation.multiSubst e_n12 (children_n12 base) S_n12

def w_n12 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 2 => 3297525202480183242043305233280201016522805820419509271274588
  | 3 => 130940414668930305141261926686317086211509400570750271259872157
  | 7 => 54095033374409453242042526726058801818488226260794528184299527
  | 9 => 149473339186735421827368443190548416276801260840039991772545024
  | 11 => 88210942355575642527365647520405941232658475132391279783040
  | 14 => 4105548165935348547201331935178845552806336368058196480
  | 15 => 42205748139697593170360542860590309449643488703393738503737600
  | 23 => 31872844348842282794052581285444380639395676419542241440194560
  | 46 => 66447012583630943518496857757591387653096510856343851349504
  | 47 => 35227369623027421373802476323093699004423060866708342083168768
  | 51 => 29075796382639688729392701407700111697146581547540480
  | 55 => 38734579540008957406377612935098226038780409709276864950231040
  | _ => 0

theorem polynomial_n12 : ∀ letter, (∑ word ∈ S_n12.T letter, w_n6 (word 0) * w_n10 (word 1) * w_n11 (word 2)) = w_n12 letter := by native_decide

theorem step_n12 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n12 base).w letter = w_n12 letter := by
  change (Realisation.multiSubst e_n12 (children_n12 base) S_n12).w letter = w_n12 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n12 base 0).w value = w_n6 value := fun value => step_n6 base correct value
  have child1 : ∀ value, (children_n12 base 1).w value = w_n10 value := fun value => step_n10 base correct value
  have child2 : ∀ value, (children_n12 base 2).w value = w_n11 value := fun value => step_n11 base correct value
  simp only [Fin.prod_univ_three, child0, child1, child2]
  exact polynomial_n12 letter

def e_n13 : Fin 3 → Nat := Fin.cases (1) (Fin.cases (3) (fun _ => 1))

def children_n13 (base : Realisation Ty typedSep graph) :
    (index : Fin 3) → Realisation Ty typedSep (strongPower graph (e_n13 index)) :=
  Fin.cases (R_R1 base) (Fin.cases (R_n7 base) (fun _ => R_R1 base))

def R_n13 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 5) :=
  Realisation.multiSubst e_n13 (children_n13 base) S_n13

def w_n13 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 665477607835923668033456
  | 2 => 2259127685403789704244
  | 3 => 105580377095792711201843
  | 5 => 100147559744040425909097
  | 7 => 12274582583709252777984
  | 9 => 813141952706424045459040
  | 11 => 11267959780788341904
  | 15 => 74897506142477107682736
  | 23 => 67958002361742605609952
  | 46 => 11267959780788341904
  | 47 => 70258463185476528530256
  | 55 => 72581395966843281937536
  | _ => 0

theorem polynomial_n13 : ∀ letter, (∑ word ∈ S_n13.T letter, w_R1 (word 0) * w_n7 (word 1) * w_R1 (word 2)) = w_n13 letter := by native_decide

theorem step_n13 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n13 base).w letter = w_n13 letter := by
  change (Realisation.multiSubst e_n13 (children_n13 base) S_n13).w letter = w_n13 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n13 base 0).w value = w_R1 value := fun value => step_R1 base correct value
  have child1 : ∀ value, (children_n13 base 1).w value = w_n7 value := fun value => step_n7 base correct value
  have child2 : ∀ value, (children_n13 base 2).w value = w_R1 value := fun value => step_R1 base correct value
  simp only [Fin.prod_univ_three, child0, child1, child2]
  exact polynomial_n13 letter

def e_n14 : Fin 2 → Nat := Fin.cases (5) (fun _ => 1)

def children_n14 (base : Realisation Ty typedSep graph) :
    (index : Fin 2) → Realisation Ty typedSep (strongPower graph (e_n14 index)) :=
  Fin.cases (R_n13 base) (fun _ => R_Rf base)

def R_n14 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 6) :=
  Realisation.multiSubst e_n14 (children_n14 base) S_n14

def w_n14 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 38688217634860476084171688672
  | 2 => 204445779880607365394610108
  | 3 => 7650799801267036758759214917
  | 5 => 6986694413168659587537886305
  | 7 => 1101845289346330259393478270
  | 9 => 49272671919583757104931823040
  | 11 => 2972489575656699021979224
  | 15 => 5569804715578434641727339624
  | 23 => 4936120998934465106708782464
  | 46 => 693159813874975640566464
  | 47 => 5146545561362088111162694656
  | 54 => 11425711217719378690656
  | 55 => 5360685176010718513694610720
  | _ => 0

theorem polynomial_n14 : ∀ letter, (∑ word ∈ S_n14.T letter, w_n13 (word 0) * w_Rf (word 1)) = w_n14 letter := by native_decide

theorem step_n14 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n14 base).w letter = w_n14 letter := by
  change (Realisation.multiSubst e_n14 (children_n14 base) S_n14).w letter = w_n14 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n14 base 0).w value = w_n13 value := fun value => step_n13 base correct value
  have child1 : ∀ value, (children_n14 base 1).w value = w_Rf value := fun value => step_Rf base correct value
  simp only [Fin.prod_univ_two, child0, child1]
  exact polynomial_n14 letter

def e_n15 : Fin 3 → Nat := Fin.cases (1) (Fin.cases (1) (fun _ => 1))

def children_n15 (base : Realisation Ty typedSep graph) :
    (index : Fin 3) → Realisation Ty typedSep (strongPower graph (e_n15 index)) :=
  Fin.cases (R_R1 base) (Fin.cases (R_Rf base) (fun _ => R_R1 base))

def R_n15 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 3) :=
  Realisation.multiSubst e_n15 (children_n15 base) S_n15

def w_n15 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 196615276420472
  | 2 => 183322205820
  | 3 => 18313439468181
  | 5 => 17031931332299
  | 7 => 1028631612372
  | 9 => 221663094285880
  | 15 => 11696130496440
  | 23 => 11135216676168
  | 47 => 11321840419344
  | 55 => 11508464162520
  | _ => 0

theorem polynomial_n15 : ∀ letter, (∑ word ∈ S_n15.T letter, w_R1 (word 0) * w_Rf (word 1) * w_R1 (word 2)) = w_n15 letter := by native_decide

theorem step_n15 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n15 base).w letter = w_n15 letter := by
  change (Realisation.multiSubst e_n15 (children_n15 base) S_n15).w letter = w_n15 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n15 base 0).w value = w_R1 value := fun value => step_R1 base correct value
  have child1 : ∀ value, (children_n15 base 1).w value = w_Rf value := fun value => step_Rf base correct value
  have child2 : ∀ value, (children_n15 base 2).w value = w_R1 value := fun value => step_R1 base correct value
  simp only [Fin.prod_univ_three, child0, child1, child2]
  exact polynomial_n15 letter

def e_n16 : Fin 3 → Nat := Fin.cases (3) (Fin.cases (6) (fun _ => 3))

def children_n16 (base : Realisation Ty typedSep graph) :
    (index : Fin 3) → Realisation Ty typedSep (strongPower graph (e_n16 index)) :=
  Fin.cases (R_n11 base) (Fin.cases (R_n14 base) (fun _ => R_n15 base))

def R_n16 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 12) :=
  Realisation.multiSubst e_n16 (children_n16 base) S_n16

def w_n16 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 2 => 45969172423976494534237708505894002639135928772533224620
  | 3 => 2182699333697681580318911818984133495148888859937704169977
  | 7 => 813943861316715513049885942088005998341327209020690479451
  | 9 => 2459873805747622316777722428454425780844412290099602436096
  | 11 => 1027845326504691317596918557539978943629342345306017920
  | 14 => 29147009616947040417331262112970721243102702745600
  | 15 => 629210934238600480734653141741373976857122934241296975360
  | 23 => 485770151521179689622189309218857149920758998478019788800
  | 46 => 860708535713144286666206495779669364459491946722030080
  | 47 => 532361624114490929468967653919269607893868017964783705600
  | 55 => 580804256281823720449862812580426366036072416400444252160
  | _ => 0

theorem polynomial_n16 : ∀ letter, (∑ word ∈ S_n16.T letter, w_n11 (word 0) * w_n14 (word 1) * w_n15 (word 2)) = w_n16 letter := by native_decide

theorem step_n16 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n16 base).w letter = w_n16 letter := by
  change (Realisation.multiSubst e_n16 (children_n16 base) S_n16).w letter = w_n16 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n16 base 0).w value = w_n11 value := fun value => step_n11 base correct value
  have child1 : ∀ value, (children_n16 base 1).w value = w_n14 value := fun value => step_n14 base correct value
  have child2 : ∀ value, (children_n16 base 2).w value = w_n15 value := fun value => step_n15 base correct value
  simp only [Fin.prod_univ_three, child0, child1, child2]
  exact polynomial_n16 letter

def e_n17 : Fin 3 → Nat := Fin.cases (9) (Fin.cases (13) (fun _ => 12))

def children_n17 (base : Realisation Ty typedSep graph) :
    (index : Fin 3) → Realisation Ty typedSep (strongPower graph (e_n17 index)) :=
  Fin.cases (R_n5 base) (Fin.cases (R_n12 base) (fun _ => R_n16 base))

def R_n17 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 34) :=
  Realisation.multiSubst e_n17 (children_n17 base) S_n17

def w_n17 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 444925695374004011249274871569026681953674131192825978826512273716826819129796598139740504323274648695278530333447174734584995069110867113969454092369692852777920
  | 3 => 4119396145496401719660868995381496590916757689821348252630520647693039510621297287106928151138724740467018423108992152255712750545025696275603921073603333241521311
  | 7 => 4251811909717373990519623319689549764953522333230101488289842088964760923431232418141066007790507645755726373634071519280460617521784840688444807821437320019462049
  | 8 => 7735249070164857162531882878496158972986529007152553298364506255800815469388780868402941861128662161603544363517560866594371553992277727714671752262656000
  | 9 => 4875033911799537471564686425215602512046078259768373586239597695305067254410543013671192587497536033763213293629378823444707818347698538447462454609010038085658624
  | 10 => 2083224070861773431673505328283397539767822232452715335154430210662865968368521331811792448878691870153583327875334105470171540331729253032564944546037760
  | 11 => 57246765781148079464743634918273573524588700697179971437569595637917340683081338069979235645078858491283140145353210681202952963820304577003798388738338153693184
  | 14 => 1054135762417778291824861350522691398587364390913329728271733245681692484412601436531433080811670489645632637862670227735362047357223479302829032428446679040
  | 15 => 4623551675538861308478221737960291793301878276698672005357702897058719433127953788242239841515732282151475616841015676113229790177157464890118892904054719504056320
  | 23 => 2263214036798231375613878942630799007868534456733167515791125381873848742838726775183419441246099412094157559996157383413729730660490565120140386034675031308500992
  | 46 => 44570392019342324288790680969431989286602580087174746749173432403208981901230799554998942307248867654676698433014142328273308787261667586890595519282953148432384
  | 47 => 2974265519299322935205748432220875248797495641447700978046413277239820200779589301318891873209880144391951300102622814631251513570805758095496145099310997283274752
  | 50 => 277032149479070062810730772147486221913494095429306213346669100810766851639125670235333948694389226583524880133136918002507459722943570583919903375360
  | 51 => 57105965156317218301527419755196126097130611867497352021415378287045481657851240284314109673171910755657253066900599690194905826761334185239535234087649280
  | 54 => 1428908200815749244040996553646795092780767589546170593079593571689031731320367286472357339624926296019648172158288967062587605052610634682085895245633098350592
  | 55 => 3773919500416179644444557029087346529623303199395260891396358118944397196508408335292035873666270599083208606691664906776453923307122651994013581214677792077119488
  | _ => 0

theorem polynomial_n17 : ∀ letter, (∑ word ∈ S_n17.T letter, w_n5 (word 0) * w_n12 (word 1) * w_n16 (word 2)) = w_n17 letter := by native_decide

theorem step_n17 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n17 base).w letter = w_n17 letter := by
  change (Realisation.multiSubst e_n17 (children_n17 base) S_n17).w letter = w_n17 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n17 base 0).w value = w_n5 value := fun value => step_n5 base correct value
  have child1 : ∀ value, (children_n17 base 1).w value = w_n12 value := fun value => step_n12 base correct value
  have child2 : ∀ value, (children_n17 base 2).w value = w_n16 value := fun value => step_n16 base correct value
  simp only [Fin.prod_univ_three, child0, child1, child2]
  exact polynomial_n17 letter

def e_n18 : Fin 3 → Nat := Fin.cases (1) (Fin.cases (3) (fun _ => 1))

def children_n18 (base : Realisation Ty typedSep graph) :
    (index : Fin 3) → Realisation Ty typedSep (strongPower graph (e_n18 index)) :=
  Fin.cases (R_Rf base) (Fin.cases (R_n7 base) (fun _ => R_Rf base))

def R_n18 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 5) :=
  Realisation.multiSubst e_n18 (children_n18 base) S_n18

def w_n18 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 665477607835923668033456
  | 2 => 2259125144396067943476
  | 3 => 96937090637501269848251
  | 5 => 108836885338246060388913
  | 7 => 12228545988802781412528
  | 9 => 813141952706424045459040
  | 11 => 11267959780788341904
  | 15 => 74897506142477107682736
  | 23 => 67958002361742605609952
  | 46 => 11267959780788341904
  | 47 => 70258463185476528530256
  | 55 => 72581395966843281937536
  | _ => 0

theorem polynomial_n18 : ∀ letter, (∑ word ∈ S_n18.T letter, w_Rf (word 0) * w_n7 (word 1) * w_Rf (word 2)) = w_n18 letter := by native_decide

theorem step_n18 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n18 base).w letter = w_n18 letter := by
  change (Realisation.multiSubst e_n18 (children_n18 base) S_n18).w letter = w_n18 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n18 base 0).w value = w_Rf value := fun value => step_Rf base correct value
  have child1 : ∀ value, (children_n18 base 1).w value = w_n7 value := fun value => step_n7 base correct value
  have child2 : ∀ value, (children_n18 base 2).w value = w_Rf value := fun value => step_Rf base correct value
  simp only [Fin.prod_univ_three, child0, child1, child2]
  exact polynomial_n18 letter

def e_n19 : Fin 2 → Nat := Fin.cases (5) (fun _ => 1)

def children_n19 (base : Realisation Ty typedSep graph) :
    (index : Fin 2) → Realisation Ty typedSep (strongPower graph (e_n19 index)) :=
  Fin.cases (R_n18 base) (fun _ => R_Rf base)

def R_n19 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 6) :=
  Realisation.multiSubst e_n19 (children_n19 base) S_n19

def w_n19 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 38688217634860476084171688672
  | 2 => 204445627432849098357333948
  | 3 => 7132245826336968989952334749
  | 5 => 7505073510142185123700269417
  | 7 => 1102020319750630759075251486
  | 9 => 49272671919583757104931823040
  | 11 => 2972486999074869156560472
  | 15 => 5569804718155016471592758376
  | 23 => 4936120998934465106708782464
  | 46 => 693159813874975640566464
  | 47 => 5146545561362088111162694656
  | 54 => 11425711217719378690656
  | 55 => 5360685176010718513694610720
  | _ => 0

theorem polynomial_n19 : ∀ letter, (∑ word ∈ S_n19.T letter, w_n18 (word 0) * w_Rf (word 1)) = w_n19 letter := by native_decide

theorem step_n19 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n19 base).w letter = w_n19 letter := by
  change (Realisation.multiSubst e_n19 (children_n19 base) S_n19).w letter = w_n19 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n19 base 0).w value = w_n18 value := fun value => step_n18 base correct value
  have child1 : ∀ value, (children_n19 base 1).w value = w_Rf value := fun value => step_Rf base correct value
  simp only [Fin.prod_univ_two, child0, child1]
  exact polynomial_n19 letter

def e_n20 : Fin 2 → Nat := Fin.cases (6) (fun _ => 1)

def children_n20 (base : Realisation Ty typedSep graph) :
    (index : Fin 2) → Realisation Ty typedSep (strongPower graph (e_n20 index)) :=
  Fin.cases (R_n19 base) (fun _ => R_Rf base)

def R_n20 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 7) :=
  Realisation.multiSubst e_n20 (children_n20 base) S_n20

def w_n20 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 2249181234522065699546730044954000
  | 2 => 17270942110753329274150955628756
  | 3 => 505779228717826629773462054435675
  | 5 => 506574949417175122048612111080081
  | 7 => 92591959546992653753949472412208
  | 9 => 2986745992564682720982104966877952
  | 11 => 387149274634936719444558300216
  | 14 => 11585671174767449992325184
  | 15 => 402614829612374747365690245897864
  | 23 => 348607682003990937590495625199488
  | 46 => 42640419110333001505086599424
  | 47 => 366557386079208141950685193021056
  | 54 => 1394142431363683149076463808
  | 55 => 384949007398825621905007506320448
  | _ => 0

theorem polynomial_n20 : ∀ letter, (∑ word ∈ S_n20.T letter, w_n19 (word 0) * w_Rf (word 1)) = w_n20 letter := by native_decide

theorem step_n20 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n20 base).w letter = w_n20 letter := by
  change (Realisation.multiSubst e_n20 (children_n20 base) S_n20).w letter = w_n20 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n20 base 0).w value = w_n19 value := fun value => step_n19 base correct value
  have child1 : ∀ value, (children_n20 base 1).w value = w_Rf value := fun value => step_Rf base correct value
  simp only [Fin.prod_univ_two, child0, child1]
  exact polynomial_n20 letter

def e_n21 : Fin 3 → Nat := Fin.cases (1) (Fin.cases (1) (fun _ => 1))

def children_n21 (base : Realisation Ty typedSep graph) :
    (index : Fin 3) → Realisation Ty typedSep (strongPower graph (e_n21 index)) :=
  Fin.cases (R_R1 base) (Fin.cases (R_Rf base) (fun _ => R_Rf base))

def R_n21 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 3) :=
  Realisation.multiSubst e_n21 (children_n21 base) S_n21

def w_n21 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 196615276420472
  | 2 => 183669736068
  | 3 => 17103348798263
  | 5 => 18241674471969
  | 7 => 1028631612372
  | 9 => 221663094285880
  | 15 => 11696130496440
  | 23 => 11135216676168
  | 47 => 11321840419344
  | 55 => 11508464162520
  | _ => 0

theorem polynomial_n21 : ∀ letter, (∑ word ∈ S_n21.T letter, w_R1 (word 0) * w_Rf (word 1) * w_Rf (word 2)) = w_n21 letter := by native_decide

theorem step_n21 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n21 base).w letter = w_n21 letter := by
  change (Realisation.multiSubst e_n21 (children_n21 base) S_n21).w letter = w_n21 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n21 base 0).w value = w_R1 value := fun value => step_R1 base correct value
  have child1 : ∀ value, (children_n21 base 1).w value = w_Rf value := fun value => step_Rf base correct value
  have child2 : ∀ value, (children_n21 base 2).w value = w_Rf value := fun value => step_Rf base correct value
  simp only [Fin.prod_univ_three, child0, child1, child2]
  exact polynomial_n21 letter

def e_n22 : Fin 3 → Nat := Fin.cases (1) (Fin.cases (3) (fun _ => 1))

def children_n22 (base : Realisation Ty typedSep graph) :
    (index : Fin 3) → Realisation Ty typedSep (strongPower graph (e_n22 index)) :=
  Fin.cases (R_R1 base) (Fin.cases (R_n21 base) (fun _ => R_R1 base))

def R_n22 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 5) :=
  Realisation.multiSubst e_n22 (children_n22 base) S_n22

def w_n22 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 665477607835923668033456
  | 2 => 2259127685403789704244
  | 3 => 105580377095792711201843
  | 5 => 100147559744040425909097
  | 7 => 12274582583709252777984
  | 9 => 813141952706424045459040
  | 11 => 11267959780788341904
  | 15 => 74897506142477107682736
  | 23 => 67958002361742605609952
  | 46 => 11267959780788341904
  | 47 => 70258463185476528530256
  | 55 => 72581395966843281937536
  | _ => 0

theorem polynomial_n22 : ∀ letter, (∑ word ∈ S_n22.T letter, w_R1 (word 0) * w_n21 (word 1) * w_R1 (word 2)) = w_n22 letter := by native_decide

theorem step_n22 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n22 base).w letter = w_n22 letter := by
  change (Realisation.multiSubst e_n22 (children_n22 base) S_n22).w letter = w_n22 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n22 base 0).w value = w_R1 value := fun value => step_R1 base correct value
  have child1 : ∀ value, (children_n22 base 1).w value = w_n21 value := fun value => step_n21 base correct value
  have child2 : ∀ value, (children_n22 base 2).w value = w_R1 value := fun value => step_R1 base correct value
  simp only [Fin.prod_univ_three, child0, child1, child2]
  exact polynomial_n22 letter

def e_n23 : Fin 2 → Nat := Fin.cases (5) (fun _ => 1)

def children_n23 (base : Realisation Ty typedSep graph) :
    (index : Fin 2) → Realisation Ty typedSep (strongPower graph (e_n23 index)) :=
  Fin.cases (R_n22 base) (fun _ => R_Rf base)

def R_n23 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 6) :=
  Realisation.multiSubst e_n23 (children_n23 base) S_n23

def w_n23 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 38688217634860476084171688672
  | 2 => 204445779880607365394610108
  | 3 => 7650799801267036758759214917
  | 5 => 6986694413168659587537886305
  | 7 => 1101845289346330259393478270
  | 9 => 49272671919583757104931823040
  | 11 => 2972489575656699021979224
  | 15 => 5569804715578434641727339624
  | 23 => 4936120998934465106708782464
  | 46 => 693159813874975640566464
  | 47 => 5146545561362088111162694656
  | 54 => 11425711217719378690656
  | 55 => 5360685176010718513694610720
  | _ => 0

theorem polynomial_n23 : ∀ letter, (∑ word ∈ S_n23.T letter, w_n22 (word 0) * w_Rf (word 1)) = w_n23 letter := by native_decide

theorem step_n23 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n23 base).w letter = w_n23 letter := by
  change (Realisation.multiSubst e_n23 (children_n23 base) S_n23).w letter = w_n23 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n23 base 0).w value = w_n22 value := fun value => step_n22 base correct value
  have child1 : ∀ value, (children_n23 base 1).w value = w_Rf value := fun value => step_Rf base correct value
  simp only [Fin.prod_univ_two, child0, child1]
  exact polynomial_n23 letter

def e_n24 : Fin 2 → Nat := Fin.cases (6) (fun _ => 1)

def children_n24 (base : Realisation Ty typedSep graph) :
    (index : Fin 2) → Realisation Ty typedSep (strongPower graph (e_n24 index)) :=
  Fin.cases (R_n23 base) (fun _ => R_R1 base)

def R_n24 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 7) :=
  Realisation.multiSubst e_n24 (children_n24 base) S_n24

def w_n24 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 2249181234524678353522213579568528
  | 2 => 17201848583256941215548960631452
  | 3 => 521296389453204977860303725343089
  | 5 => 491088127901259356994810658109723
  | 7 => 92630713852413804804027714857928
  | 9 => 2986745992564682720982104966877952
  | 11 => 387149585105317472737921659960
  | 14 => 11585671174767449992325184
  | 15 => 402614829301904366612396882538120
  | 23 => 348607682003990937590495625199488
  | 46 => 42640419110333001505086599424
  | 47 => 366557386079208141950685193021056
  | 54 => 1394142431363683149076463808
  | 55 => 384949007398825621905007506320448
  | _ => 0

theorem polynomial_n24 : ∀ letter, (∑ word ∈ S_n24.T letter, w_n23 (word 0) * w_R1 (word 1)) = w_n24 letter := by native_decide

theorem step_n24 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n24 base).w letter = w_n24 letter := by
  change (Realisation.multiSubst e_n24 (children_n24 base) S_n24).w letter = w_n24 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n24 base 0).w value = w_n23 value := fun value => step_n23 base correct value
  have child1 : ∀ value, (children_n24 base 1).w value = w_R1 value := fun value => step_R1 base correct value
  simp only [Fin.prod_univ_two, child0, child1]
  exact polynomial_n24 letter

def e_n25 : Fin 2 → Nat := Fin.cases (7) (fun _ => 1)

def children_n25 (base : Realisation Ty typedSep graph) :
    (index : Fin 2) → Realisation Ty typedSep (strongPower graph (e_n25 index)) :=
  Fin.cases (R_n24 base) (fun _ => R_R1 base)

def R_n25 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 8) :=
  Realisation.multiSubst e_n25 (children_n25 base) S_n25

def w_n25 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 130758792820005997552284764914359143248
  | 2 => 1379698870483406152812766908342812796
  | 3 => 34960213048498161392598296446241651085
  | 5 => 33644060148417432182101460477710724937
  | 7 => 7414306023876411152155980543597989982
  | 9 => 181112750060487732375735835689724441600
  | 11 => 40865998661464456128156382351192248
  | 14 => 2114616702818554972599192583680
  | 15 => 28503984101730072264197571020052129096
  | 23 => 24120022413066047985176020752233666304
  | 46 => 2623068021991244920586907250166784
  | 47 => 25577704598509156339314204770297524224
  | 54 => 127585790360243221411582025127552
  | 55 => 27080774178751487694897004144480574592
  | _ => 0

theorem polynomial_n25 : ∀ letter, (∑ word ∈ S_n25.T letter, w_n24 (word 0) * w_R1 (word 1)) = w_n25 letter := by native_decide

theorem step_n25 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n25 base).w letter = w_n25 letter := by
  change (Realisation.multiSubst e_n25 (children_n25 base) S_n25).w letter = w_n25 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n25 base 0).w value = w_n24 value := fun value => step_n24 base correct value
  have child1 : ∀ value, (children_n25 base 1).w value = w_R1 value := fun value => step_R1 base correct value
  simp only [Fin.prod_univ_two, child0, child1]
  exact polynomial_n25 letter

def e_n26 : Fin 2 → Nat := Fin.cases (8) (fun _ => 1)

def children_n26 (base : Realisation Ty typedSep graph) :
    (index : Fin 2) → Realisation Ty typedSep (strongPower graph (e_n26 index)) :=
  Fin.cases (R_n25 base) (fun _ => R_R1 base)

def R_n26 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 9) :=
  Realisation.multiSubst e_n26 (children_n26 base) S_n26

def w_n26 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 7601834617506511398658141043632887260805200
  | 2 => 106766398243277533515319720493772120603228
  | 3 => 2315973455937088218447251711440701863400681
  | 5 => 2261555984456694993214874499336048589893347
  | 7 => 572262100907682304813843853600135193728904
  | 9 => 10986628084305647139089194560701326413377536
  | 11 => 3871489305686096363617863090071445563640
  | 14 => 257310531179214839463540523177145088
  | 15 => 1986137909116344987619123958515718397216264
  | 23 => 1642957924596656595828115744941021862507008
  | 46 => 161360652440813422534824186401259884544
  | 47 => 1757086404643223821998248758039003083945984
  | 54 => 10378986462674557731318659635936270080
  | 55 => 1875485154776290787482971359322502779284736
  | _ => 0

theorem polynomial_n26 : ∀ letter, (∑ word ∈ S_n26.T letter, w_n25 (word 0) * w_R1 (word 1)) = w_n26 letter := by native_decide

theorem step_n26 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n26 base).w letter = w_n26 letter := by
  change (Realisation.multiSubst e_n26 (children_n26 base) S_n26).w letter = w_n26 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n26 base 0).w value = w_n25 value := fun value => step_n25 base correct value
  have child1 : ∀ value, (children_n26 base 1).w value = w_R1 value := fun value => step_R1 base correct value
  simp only [Fin.prod_univ_two, child0, child1]
  exact polynomial_n26 letter

def e_n27 : Fin 2 → Nat := Fin.cases (9) (fun _ => 1)

def children_n27 (base : Realisation Ty typedSep graph) :
    (index : Fin 2) → Realisation Ty typedSep (strongPower graph (e_n27 index)) :=
  Fin.cases (R_n26 base) (fun _ => R_R1 base)

def R_n27 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 10) :=
  Realisation.multiSubst e_n27 (children_n27 base) S_n27

def w_n27 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 441944183013514512374102396225814866239972638160
  | 2 => 8035322355540217605093137930867159567408878908
  | 3 => 151938841749157381053241346147146523917182947397
  | 5 => 149813861841424020808031879787779772568488220065
  | 7 => 42948496706382664745701683543124311246716905230
  | 9 => 666730842147573081344056796734690012064371624960
  | 11 => 342493973791303621176142149256187529783020472
  | 14 => 26092094030556857756780249604103009975296
  | 15 => 136663165984872561679555668725363118183692958792
  | 23 => 110542681231432843559829102084972849708563819520
  | 46 => 9926261895549078500652244650659903057608704
  | 47 => 119229368145518482833080713884078458695185973248
  | 54 => 791569140539720902310553270304293735307776
  | 55 => 128294481797304732389346673222406645920143730176
  | _ => 0

theorem polynomial_n27 : ∀ letter, (∑ word ∈ S_n27.T letter, w_n26 (word 0) * w_R1 (word 1)) = w_n27 letter := by native_decide

theorem step_n27 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n27 base).w letter = w_n27 letter := by
  change (Realisation.multiSubst e_n27 (children_n27 base) S_n27).w letter = w_n27 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n27 base 0).w value = w_n26 value := fun value => step_n26 base correct value
  have child1 : ∀ value, (children_n27 base 1).w value = w_R1 value := fun value => step_R1 base correct value
  simp only [Fin.prod_univ_two, child0, child1]
  exact polynomial_n27 letter

def e_n28 : Fin 2 → Nat := Fin.cases (10) (fun _ => 1)

def children_n28 (base : Realisation Ty typedSep graph) :
    (index : Fin 2) → Realisation Ty typedSep (strongPower graph (e_n28 index)) :=
  Fin.cases (R_n27 base) (fun _ => R_Rf base)

def R_n28 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 11) :=
  Realisation.multiSubst e_n28 (children_n28 base) S_n28

def w_n28 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 25693214312563104073252689515123318837882249274828368
  | 2 => 594169443489308258587229519676537707851179403078740
  | 3 => 10087943249031641350297740792937385788852245743406755
  | 5 => 9609642658237388382665767597159042303669300127059065
  | 7 => 3151622670853511635760696116854127590735892006220352
  | 9 => 40477473177267935073877720137644252184472528811253760
  | 11 => 28869387270839232339963394176197157728284907809656
  | 14 => 2381274981544028002943619677635994157127443456
  | 15 => 9308234170404724907835753693367321775525274609029256
  | 23 => 7364118373801789005539653926234003025300801036308480
  | 46 => 610623926766597113046123481929994596491857035264
  | 47 => 8010578884777354094442666787181946137326333158033408
  | 54 => 57956745703020959631254470035719521274006289408
  | 55 => 8689127798131301271015662328618014548327600712174592
  | _ => 0

theorem polynomial_n28 : ∀ letter, (∑ word ∈ S_n28.T letter, w_n27 (word 0) * w_Rf (word 1)) = w_n28 letter := by native_decide

theorem step_n28 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n28 base).w letter = w_n28 letter := by
  change (Realisation.multiSubst e_n28 (children_n28 base) S_n28).w letter = w_n28 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n28 base 0).w value = w_n27 value := fun value => step_n27 base correct value
  have child1 : ∀ value, (children_n28 base 1).w value = w_Rf value := fun value => step_Rf base correct value
  simp only [Fin.prod_univ_two, child0, child1]
  exact polynomial_n28 letter

def e_n29 : Fin 2 → Nat := Fin.cases (11) (fun _ => 1)

def children_n29 (base : Realisation Ty typedSep graph) :
    (index : Fin 2) → Realisation Ty typedSep (strongPower graph (e_n29 index)) :=
  Fin.cases (R_n28 base) (fun _ => R_Rf base)

def R_n29 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 12) :=
  Realisation.multiSubst e_n29 (children_n29 base) S_n29

def w_n29 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 1493729980833861249384211080532903927877058924737940993232
  | 2 => 43114411793176063025558044114195158850186520538525805020
  | 3 => 663332124219658593486790734010225541378735932430460295845
  | 5 => 612361831031876360040109038296219554662418338826976588433
  | 7 => 227083307603665053282633508033574936299074627366575649822
  | 9 => 2458435907593160461163532395879352026986174122815777308672
  | 11 => 2349143484358473809239916007400289672637789407021649672
  | 14 => 202840039076240035300186910352552513066366961434624
  | 15 => 628666792207322064392470431176912556646925006540085625080
  | 23 => 486588047653505524578072150064580922751804208513346969600
  | 46 => 37563141478973988006145332114405547597793077381300224
  | 47 => 533822928477713400638647098299855870298821854764194439168
  | 54 => 4125671690265503572238927156778116996962671555520512
  | 55 => 583687329188899195067729422241072164272819303289366849536
  | _ => 0

theorem polynomial_n29 : ∀ letter, (∑ word ∈ S_n29.T letter, w_n28 (word 0) * w_Rf (word 1)) = w_n29 letter := by native_decide

theorem step_n29 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n29 base).w letter = w_n29 letter := by
  change (Realisation.multiSubst e_n29 (children_n29 base) S_n29).w letter = w_n29 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n29 base 0).w value = w_n28 value := fun value => step_n28 base correct value
  have child1 : ∀ value, (children_n29 base 1).w value = w_Rf value := fun value => step_Rf base correct value
  simp only [Fin.prod_univ_two, child0, child1]
  exact polynomial_n29 letter

def e_n30 : Fin 2 → Nat := Fin.cases (12) (fun _ => 1)

def children_n30 (base : Realisation Ty typedSep graph) :
    (index : Fin 2) → Realisation Ty typedSep (strongPower graph (e_n30 index)) :=
  Fin.cases (R_n29 base) (fun _ => R_R1 base)

def R_n30 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 13) :=
  Realisation.multiSubst e_n30 (children_n30 base) S_n30

def w_n30 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 86841868197250497086643064652692406644788752367023657535302960
  | 2 => 3065476744666158993837881397886025647195906723199367777252540
  | 3 => 42561985859922014169720733087949777226562983093139243310003073
  | 5 => 39515492087127570283211590151292360583895240779012292729456123
  | 7 => 16133793514470888686647432701966955005438483168826324755432600
  | 9 => 149380139645672557910359967101926976660373791702986624400580608
  | 11 => 185845892648936910314549255011526216848020666529689014745624
  | 14 => 16455659138119895237982180587123142780461482858015420416
  | 15 => 42159315839346306039374545603308640628155554839545233177908712
  | 23 => 31932404069431855955642343072628937943693638784009716545732608
  | 46 => 2310734211220563846186036250349771666025838948188064579584
  | 47 => 35331505278534482261306836748435596672666305778209383310852096
  | 54 => 287700414064123120965830937603396859814397734916740444160
  | 55 => 38940264385591282908874475395951649038264373102563739766165504
  | _ => 0

theorem polynomial_n30 : ∀ letter, (∑ word ∈ S_n30.T letter, w_n29 (word 0) * w_R1 (word 1)) = w_n30 letter := by native_decide

theorem step_n30 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n30 base).w letter = w_n30 letter := by
  change (Realisation.multiSubst e_n30 (children_n30 base) S_n30).w letter = w_n30 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n30 base 0).w value = w_n29 value := fun value => step_n29 base correct value
  have child1 : ∀ value, (children_n30 base 1).w value = w_R1 value := fun value => step_R1 base correct value
  simp only [Fin.prod_univ_two, child0, child1]
  exact polynomial_n30 letter

def e_n31 : Fin 2 → Nat := Fin.cases (13) (fun _ => 1)

def children_n31 (base : Realisation Ty typedSep graph) :
    (index : Fin 2) → Realisation Ty typedSep (strongPower graph (e_n31 index)) :=
  Fin.cases (R_n30 base) (fun _ => R_R1 base)

def R_n31 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 14) :=
  Realisation.multiSubst e_n31 (children_n31 base) S_n31

def w_n31 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 5048827297250500920656140159593507440285322800565148459133324945296
  | 2 => 215256603882952949034407826429332375109671557112890536064927643292
  | 3 => 2719655156188855515338858057238921209129745277331320930423997335773
  | 5 => 2532170980745907253225348808316140357183457261187139481661848302025
  | 7 => 1131712237014307247190079141524813520426838977408543744209990297390
  | 9 => 9080735219524762641097157243101053706429635550565200338614915743744
  | 11 => 14352441616137466167602470764163789177995595783703403696273818808
  | 14 => 1287328509035550746347750460611968800355279939081223776387072
  | 15 => 2810231696339517434612248752100736210937507858794864722016915061576
  | 23 => 2083445772609478122749378047221549957802971558496984307592102985728
  | 46 => 142147125737444205561980205976516553807245508736736980677689344
  | 47 => 2324924340315039184507656376058118119249359491039156860892566274048
  | 54 => 19749534941885228804707344144735385281840892451395327836266496
  | 55 => 2582747203625399159177237026914200021441989686422546972849640284160
  | _ => 0

theorem polynomial_n31 : ∀ letter, (∑ word ∈ S_n31.T letter, w_n30 (word 0) * w_R1 (word 1)) = w_n31 letter := by native_decide

theorem step_n31 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n31 base).w letter = w_n31 letter := by
  change (Realisation.multiSubst e_n31 (children_n31 base) S_n31).w letter = w_n31 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n31 base 0).w value = w_n30 value := fun value => step_n30 base correct value
  have child1 : ∀ value, (children_n31 base 1).w value = w_R1 value := fun value => step_R1 base correct value
  simp only [Fin.prod_univ_two, child0, child1]
  exact polynomial_n31 letter

def e_n32 : Fin 2 → Nat := Fin.cases (14) (fun _ => 1)

def children_n32 (base : Realisation Ty typedSep graph) :
    (index : Fin 2) → Realisation Ty typedSep (strongPower graph (e_n32 index)) :=
  Fin.cases (R_n31 base) (fun _ => R_R1 base)

def R_n32 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 15) :=
  Realisation.multiSubst e_n32 (children_n32 base) S_n32

def w_n32 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 293533177128753884913959313223483010630654013867780146071523000671999568
  | 2 => 14954177231271334897013537041177333159129889242999652797923780843399036
  | 3 => 173175472243934353751888485484025289853483065943158918115676957919813977
  | 5 => 161303367935439386868754566311611171060711933471173044187831439953295139
  | 7 => 78525680969241731953315601135896432533625661499088541730087645448825272
  | 9 => 552266771872925331543099433458703927007059294143492277194713715109199872
  | 11 => 1086621618996863268393174222172780601208296495018094334001795215819704
  | 14 => 97911977884740513263504845330707017034881811820007063344944857088
  | 15 => 186348576560432014322304033817779202595499210592078352881880491863948360
  | 23 => 135260501647016754700655388057502684005315035680457657721292939406671872
  | 46 => 8744322586864617749350774350851392324006514715449112103368737685504
  | 47 => 152227911231418059792245507074095662682063248899037886598022631478493184
  | 54 => 1339023548551708537582251664304968065882484620953371423156972535808
  | 55 => 170445635797926044798732201930728291511944614308821163496981484460654592
  | _ => 0

theorem polynomial_n32 : ∀ letter, (∑ word ∈ S_n32.T letter, w_n31 (word 0) * w_R1 (word 1)) = w_n32 letter := by native_decide

theorem step_n32 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n32 base).w letter = w_n32 letter := by
  change (Realisation.multiSubst e_n32 (children_n32 base) S_n32).w letter = w_n32 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n32 base 0).w value = w_n31 value := fun value => step_n31 base correct value
  have child1 : ∀ value, (children_n32 base 1).w value = w_R1 value := fun value => step_R1 base correct value
  simp only [Fin.prod_univ_two, child0, child1]
  exact polynomial_n32 letter

def e_n33 : Fin 2 → Nat := Fin.cases (15) (fun _ => 1)

def children_n33 (base : Realisation Ty typedSep graph) :
    (index : Fin 2) → Realisation Ty typedSep (strongPower graph (e_n33 index)) :=
  Fin.cases (R_n32 base) (fun _ => R_R1 base)

def R_n33 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 16) :=
  Realisation.multiSubst e_n33 (children_n33 base) S_n33

def w_n33 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 17065946619878898672712089312221691505553326962863214919668738987416208065104
  | 2 => 1029275499756029015217601142755823885855601248749614351895130034333021568860
  | 3 => 10994350481457183449953788398778104315070037957077186170062456121756461301013
  | 5 => 10223073735569039487245980569147567124549798260383230077595908498247189061217
  | 7 => 5397861416035151653892298909350568548759484063175917362054806682371831522014
  | 9 => 33603303622092414866024449341264929468079478099826042737798636062409780559872
  | 11 => 80906316905057355049895553349651387757662062233986391332871327922730353912
  | 14 => 7281640364214002990576973339803673563449258784380785969577023894847488
  | 15 => 12300876828481682257713166487972529651342967844559190689981454495163921742600
  | 23 => 8743529377326953979083755113782153169674728413000550376529105127103190269952
  | 46 => 537915748253563825469062234966974250203584759235567580150831267461464064
  | 47 => 9924450693991059652364477438697194567534960943534715801039399905151715377152
  | 54 => 89880345837556192338643075385542489738564690458386277516659052374556672
  | 55 => 11199492698182901002085307012074127969831173957305973926484770734691699949568
  | _ => 0

theorem polynomial_n33 : ∀ letter, (∑ word ∈ S_n33.T letter, w_n32 (word 0) * w_R1 (word 1)) = w_n33 letter := by native_decide

theorem step_n33 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n33 base).w letter = w_n33 letter := by
  change (Realisation.multiSubst e_n33 (children_n33 base) S_n33).w letter = w_n33 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n33 base 0).w value = w_n32 value := fun value => step_n32 base correct value
  have child1 : ∀ value, (children_n33 base 1).w value = w_R1 value := fun value => step_R1 base correct value
  simp only [Fin.prod_univ_two, child0, child1]
  exact polynomial_n33 letter

def e_n34 : Fin 2 → Nat := Fin.cases (16) (fun _ => 1)

def children_n34 (base : Realisation Ty typedSep graph) :
    (index : Fin 2) → Realisation Ty typedSep (strongPower graph (e_n34 index)) :=
  Fin.cases (R_n33 base) (fun _ => R_Rf base)

def R_n34 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 17) :=
  Realisation.multiSubst e_n34 (children_n34 base) S_n34

def w_n34 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 992227911698621381394810618346416803874034485644121124770673341298942320651752912
  | 2 => 70617322396472492102770908245010757345956971529515671123748839008692263957487028
  | 3 => 705370276424171268967015463618099212649223694290088090959551901593804598375888563
  | 5 => 635835214651677993571828550657525604729213925130197306631955265279792610292045753
  | 7 => 367781944025537609575008649740196398793248024329096557323079277532218690011856400
  | 9 => 2045622211236840767504552011400162420812317616058711926644862778583628638034591744
  | 11 => 5938679342142393516659428327515013682371649755512753601243042936794715743207864
  | 14 => 531692475994957587967272119445741942530711651097409998133241378793863184384
  | 15 => 808742643765847169996564843241083160575858929839919512977307287024116385562017352
  | 23 => 563074764259837078316674143526090469552293009236582906216891735367280735200346112
  | 46 => 33090425169566232287554832446228387975523720049135175260558536249159423361024
  | 47 => 644586258764355734249001985750939259497113248195705184552867541532596440628592640
  | 54 => 5983387252592938467898212453232603603869075847978152088585848891971352330240
  | 55 => 733085226836598660487905149293712090904332133252198226023704326878681078778232832
  | _ => 0

theorem polynomial_n34 : ∀ letter, (∑ word ∈ S_n34.T letter, w_n33 (word 0) * w_Rf (word 1)) = w_n34 letter := by native_decide

theorem step_n34 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n34 base).w letter = w_n34 letter := by
  change (Realisation.multiSubst e_n34 (children_n34 base) S_n34).w letter = w_n34 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n34 base 0).w value = w_n33 value := fun value => step_n33 base correct value
  have child1 : ∀ value, (children_n34 base 1).w value = w_Rf value := fun value => step_Rf base correct value
  simp only [Fin.prod_univ_two, child0, child1]
  exact polynomial_n34 letter

def e_n35 : Fin 3 → Nat := Fin.cases (1) (Fin.cases (1) (fun _ => 1))

def children_n35 (base : Realisation Ty typedSep graph) :
    (index : Fin 3) → Realisation Ty typedSep (strongPower graph (e_n35 index)) :=
  Fin.cases (R_Rf base) (Fin.cases (R_R1 base) (fun _ => R_R1 base))

def R_n35 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 3) :=
  Realisation.multiSubst e_n35 (children_n35 base) S_n35

def w_n35 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 196615276420472
  | 2 => 183322205820
  | 3 => 18313439468181
  | 5 => 17031931332299
  | 7 => 1028631612372
  | 9 => 221663094285880
  | 15 => 11696130496440
  | 23 => 11135216676168
  | 47 => 11321840419344
  | 55 => 11508464162520
  | _ => 0

theorem polynomial_n35 : ∀ letter, (∑ word ∈ S_n35.T letter, w_Rf (word 0) * w_R1 (word 1) * w_R1 (word 2)) = w_n35 letter := by native_decide

theorem step_n35 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n35 base).w letter = w_n35 letter := by
  change (Realisation.multiSubst e_n35 (children_n35 base) S_n35).w letter = w_n35 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n35 base 0).w value = w_Rf value := fun value => step_Rf base correct value
  have child1 : ∀ value, (children_n35 base 1).w value = w_R1 value := fun value => step_R1 base correct value
  have child2 : ∀ value, (children_n35 base 2).w value = w_R1 value := fun value => step_R1 base correct value
  simp only [Fin.prod_univ_three, child0, child1, child2]
  exact polynomial_n35 letter

def e_n36 : Fin 3 → Nat := Fin.cases (3) (Fin.cases (6) (fun _ => 3))

def children_n36 (base : Realisation Ty typedSep graph) :
    (index : Fin 3) → Realisation Ty typedSep (strongPower graph (e_n36 index)) :=
  Fin.cases (R_n35 base) (Fin.cases (R_n9 base) (fun _ => R_n21 base))

def R_n36 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 12) :=
  Realisation.multiSubst e_n36 (children_n36 base) S_n36

def w_n36 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 2 => 46022035973181148607756027340240475231996117504215513324
  | 3 => 2158652458231908245619649599383781692994205140849167111833
  | 7 => 837937873233284193675629842854011327903150739377545248891
  | 9 => 2459873805747622316777722428454425780844412290099602436096
  | 11 => 1027277015899884838600120919460102049480803236177462400
  | 14 => 29147009616947040417331262112970721243102702745600
  | 15 => 629211501260086719285258113559223647007676101010312755200
  | 23 => 485770151521179689622189309218857149920758998478019788800
  | 46 => 859945162776941982782287064839143720558531783981381120
  | 47 => 532362387487427131772851573350210133537768978127524354560
  | 55 => 580804256281823720449862812580426366036072416400444252160
  | _ => 0

theorem polynomial_n36 : ∀ letter, (∑ word ∈ S_n36.T letter, w_n35 (word 0) * w_n9 (word 1) * w_n21 (word 2)) = w_n36 letter := by native_decide

theorem step_n36 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n36 base).w letter = w_n36 letter := by
  change (Realisation.multiSubst e_n36 (children_n36 base) S_n36).w letter = w_n36 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n36 base 0).w value = w_n35 value := fun value => step_n35 base correct value
  have child1 : ∀ value, (children_n36 base 1).w value = w_n9 value := fun value => step_n9 base correct value
  have child2 : ∀ value, (children_n36 base 2).w value = w_n21 value := fun value => step_n21 base correct value
  simp only [Fin.prod_univ_three, child0, child1, child2]
  exact polynomial_n36 letter

def e_n37 : Fin 3 → Nat := Fin.cases (7) (Fin.cases (17) (fun _ => 12))

def children_n37 (base : Realisation Ty typedSep graph) :
    (index : Fin 3) → Realisation Ty typedSep (strongPower graph (e_n37 index)) :=
  Fin.cases (R_n20 base) (Fin.cases (R_n34 base) (fun _ => R_n36 base))

def R_n37 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 36) :=
  Realisation.multiSubst e_n37 (children_n37 base) S_n37

def w_n37 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 1815647751527775838430987736462862423348580816227254668063195450604946674049931612607404561905876356215407267111794929210590062317947698687219608354872908435032672826628800
  | 3 => 15386055334918402515058918280518896721485005041878731726621686756628106354985772905477557977164602567101675083889576768001630050554235314272933882962931425499452223830225113
  | 7 => 17054148531314350805037553677826165313998820575745532831663074600169966754150481158821722595558542406053483275905817648578247071732006110948415654033172006713732781156398183
  | 8 => 6746844926930961729906854846655158328417957116449600754511080412420054778087292305218082944498431351630407181867463463993365943506322050927656902269281068540846080
  | 9 => 18373679375443337353175065025665928803274421350390620805456587898958527552418675258460485800238463019113047871637280227619552698600052738059890491071314156515063452504221696
  | 10 => 2033062997242380918281881936679593549264683591855494098678051433097250770749678882097689200103706924480268342974559783384487351842276596988870688987046918107430912
  | 11 => 276566242263301956240067806819431862861783675995794866170919504456584418551481290961694298392749924811441293982402160158791751522071785748500363597653362400796784120766464
  | 14 => 7595433880653718287268764703687595153777349195668702888853442994449002906047423445707629577935808229711494936232855794084388331405825905282207716083370270163621642240
  | 15 => 18776357736723646657337198281561866229459605034623763649793384118464857757944245902724249629593295392319372957800353621293085181705865725743969666489702633608494643178168320
  | 23 => 8859040923753683823310484052024771657099531821368974580390516406683345347386076950984406278403819139807682917517617415968187712513692509081544004194482154020418852241801216
  | 46 => 181836737763610861348404310175128051258117937319681714298450621856720277596698735164194469233396328244433569952193207538878234677350918103411873094839337563790607627321344
  | 47 => 11860281070615110041145569411406232395037527142300345039309099470612651758008729867607939704020066631956369853392980201156988160032006623663864662221042732232943872894304256
  | 51 => 889523913308008434137146679542327310491144655248234537087497870647699403739023930457937484639005990794555505402114237659523136913990532722133123212402867294382850048
  | 54 => 11007207256078829742645404165439828366393568967281747233843187045161978406429025981505456119540867472844426789248860987397384585182097908603016303321443354347510909894656
  | 55 => 15269570771274775688181302744868264151712006886533212332384832556016994970907778617376051249686618677710631837913540907517967554585868211196011091585577890351795915691393024
  | _ => 0

theorem polynomial_n37 : ∀ letter, (∑ word ∈ S_n37.T letter, w_n20 (word 0) * w_n34 (word 1) * w_n36 (word 2)) = w_n37 letter := by native_decide

theorem step_n37 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n37 base).w letter = w_n37 letter := by
  change (Realisation.multiSubst e_n37 (children_n37 base) S_n37).w letter = w_n37 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n37 base 0).w value = w_n20 value := fun value => step_n20 base correct value
  have child1 : ∀ value, (children_n37 base 1).w value = w_n34 value := fun value => step_n34 base correct value
  have child2 : ∀ value, (children_n37 base 2).w value = w_n36 value := fun value => step_n36 base correct value
  simp only [Fin.prod_univ_three, child0, child1, child2]
  exact polynomial_n37 letter

def e_n38 : Fin 2 → Nat := Fin.cases (6) (fun _ => 1)

def children_n38 (base : Realisation Ty typedSep graph) :
    (index : Fin 2) → Realisation Ty typedSep (strongPower graph (e_n38 index)) :=
  Fin.cases (R_n19 base) (fun _ => R_R1 base)

def R_n38 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 7) :=
  Realisation.multiSubst e_n38 (children_n38 base) S_n38

def w_n38 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 2249181234522065699546730044954000
  | 2 => 17201839488681026278906176754332
  | 3 => 490361014690014196333652913393801
  | 5 => 522188281824186021536872832914163
  | 7 => 92465943789866490700742670494424
  | 9 => 2986745992564682720982104966877952
  | 11 => 387149274634936719444558300216
  | 14 => 11585671174767449992325184
  | 15 => 402614829612374747365690245897864
  | 23 => 348607682003990937590495625199488
  | 46 => 42640419110333001505086599424
  | 47 => 366557386079208141950685193021056
  | 54 => 1394142431363683149076463808
  | 55 => 384949007398825621905007506320448
  | _ => 0

theorem polynomial_n38 : ∀ letter, (∑ word ∈ S_n38.T letter, w_n19 (word 0) * w_R1 (word 1)) = w_n38 letter := by native_decide

theorem step_n38 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n38 base).w letter = w_n38 letter := by
  change (Realisation.multiSubst e_n38 (children_n38 base) S_n38).w letter = w_n38 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n38 base 0).w value = w_n19 value := fun value => step_n19 base correct value
  have child1 : ∀ value, (children_n38 base 1).w value = w_R1 value := fun value => step_R1 base correct value
  simp only [Fin.prod_univ_two, child0, child1]
  exact polynomial_n38 letter

def e_n39 : Fin 2 → Nat := Fin.cases (7) (fun _ => 1)

def children_n39 (base : Realisation Ty typedSep graph) :
    (index : Fin 2) → Realisation Ty typedSep (strongPower graph (e_n39 index)) :=
  Fin.cases (R_n38 base) (fun _ => R_R1 base)

def R_n39 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 8) :=
  Realisation.multiSubst e_n39 (children_n39 base) S_n39

def w_n39 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 130758792819539291334682214675562163024
  | 2 => 1379698327928290795437468350585464956
  | 3 => 33114701379654515432582799036853494117
  | 5 => 35509913883018560497562056764254695185
  | 7 => 7393964501140750371688730462996504766
  | 9 => 181112750060487732375735835689724441600
  | 11 => 40865970655485502046645529508561080
  | 14 => 2114616702818554972599192583680
  | 15 => 28503984129736051218279081872894760264
  | 23 => 24120022413066047985176020752233666304
  | 46 => 2623068021991244920586907250166784
  | 47 => 25577704598509156339314204770297524224
  | 54 => 127585790360243221411582025127552
  | 55 => 27080774178751487694897004144480574592
  | _ => 0

theorem polynomial_n39 : ∀ letter, (∑ word ∈ S_n39.T letter, w_n38 (word 0) * w_R1 (word 1)) = w_n39 letter := by native_decide

theorem step_n39 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n39 base).w letter = w_n39 letter := by
  change (Realisation.multiSubst e_n39 (children_n39 base) S_n39).w letter = w_n39 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n39 base 0).w value = w_n38 value := fun value => step_n38 base correct value
  have child1 : ∀ value, (children_n39 base 1).w value = w_R1 value := fun value => step_R1 base correct value
  simp only [Fin.prod_univ_two, child0, child1]
  exact polynomial_n39 letter

def e_n40 : Fin 2 → Nat := Fin.cases (8) (fun _ => 1)

def children_n40 (base : Realisation Ty typedSep graph) :
    (index : Fin 2) → Realisation Ty typedSep (strongPower graph (e_n40 index)) :=
  Fin.cases (R_n39 base) (fun _ => R_R1 base)

def R_n40 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 9) :=
  Realisation.multiSubst e_n40 (children_n40 base) S_n40

def w_n40 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 7601834617450980903332160530945403590498384
  | 2 => 106766365876067016640381534433642020512348
  | 3 => 2205875765327961074463711675561533894609793
  | 5 => 2373497879263222079642409832653330498685691
  | 7 => 570417929133023374570767254909635024125144
  | 9 => 10986628084305647139089194560701326413377536
  | 11 => 3871487061117470711399740733820623927544
  | 14 => 257310531179214839463540523177145088
  | 15 => 1986137911360913613271342080871969218852360
  | 23 => 1642957924596656595828115744941021862507008
  | 46 => 161360652440813422534824186401259884544
  | 47 => 1757086404643223821998248758039003083945984
  | 54 => 10378986462674557731318659635936270080
  | 55 => 1875485154776290787482971359322502779284736
  | _ => 0

theorem polynomial_n40 : ∀ letter, (∑ word ∈ S_n40.T letter, w_n39 (word 0) * w_R1 (word 1)) = w_n40 letter := by native_decide

theorem step_n40 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n40 base).w letter = w_n40 letter := by
  change (Realisation.multiSubst e_n40 (children_n40 base) S_n40).w letter = w_n40 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n40 base 0).w value = w_n39 value := fun value => step_n39 base correct value
  have child1 : ∀ value, (children_n40 base 1).w value = w_R1 value := fun value => step_R1 base correct value
  simp only [Fin.prod_univ_two, child0, child1]
  exact polynomial_n40 letter

def e_n41 : Fin 2 → Nat := Fin.cases (9) (fun _ => 1)

def children_n41 (base : Realisation Ty typedSep graph) :
    (index : Fin 2) → Realisation Ty typedSep (strongPower graph (e_n41 index)) :=
  Fin.cases (R_n40 base) (fun _ => R_R1 base)

def R_n41 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 10) :=
  Realisation.multiSubst e_n41 (children_n41 base) S_n41

def w_n41 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 441944183008010198911419843964146077249876581840
  | 2 => 8035320424609539799884950565077978186287250748
  | 3 => 145370743762509569376765320955088794217558330269
  | 5 => 156529815820238382167440864337064068543384527401
  | 7 => 42800642650651106330659463813355715342662899502
  | 9 => 666730842147573081344056796734690012064371624960
  | 11 => 342493805170061167854453989793328397663787960
  | 14 => 26092094030556857756780249604103009975296
  | 15 => 136663166153493804132877356884825977315812191304
  | 23 => 110542681231432843559829102084972849708563819520
  | 46 => 9926261895549078500652244650659903057608704
  | 47 => 119229368145518482833080713884078458695185973248
  | 54 => 791569140539720902310553270304293735307776
  | 55 => 128294481797304732389346673222406645920143730176
  | _ => 0

theorem polynomial_n41 : ∀ letter, (∑ word ∈ S_n41.T letter, w_n40 (word 0) * w_R1 (word 1)) = w_n41 letter := by native_decide

theorem step_n41 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n41 base).w letter = w_n41 letter := by
  change (Realisation.multiSubst e_n41 (children_n41 base) S_n41).w letter = w_n41 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n41 base 0).w value = w_n40 value := fun value => step_n40 base correct value
  have child1 : ∀ value, (children_n41 base 1).w value = w_R1 value := fun value => step_R1 base correct value
  simp only [Fin.prod_univ_two, child0, child1]
  exact polynomial_n41 letter

def e_n42 : Fin 2 → Nat := Fin.cases (10) (fun _ => 1)

def children_n42 (base : Realisation Ty typedSep graph) :
    (index : Fin 2) → Realisation Ty typedSep (strongPower graph (e_n42 index)) :=
  Fin.cases (R_n41 base) (fun _ => R_Rf base)

def R_n42 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 11) :=
  Realisation.multiSubst e_n42 (children_n42 base) S_n42

def w_n42 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 25693214312072123365938508465045246781994056042841680
  | 2 => 594169327643122243663764318666015770890787321619540
  | 3 => 9693890207546509748946381335695770011069961175449323
  | 5 => 10010296324743144677507289226425697320589753032140097
  | 7 => 3145022162170053664508180195917682344446308982542640
  | 9 => 40477473177267935073877720137644252184472528811253760
  | 11 => 28869375110953114134613515163465024596349771414392
  | 14 => 2381274981544028002943619677635994157127443456
  | 15 => 9308234182564611026041103572380053908657209745424520
  | 23 => 7364118373801789005539653926234003025300801036308480
  | 46 => 610623926766597113046123481929994596491857035264
  | 47 => 8010578884777354094442666787181946137326333158033408
  | 54 => 57956745703020959631254470035719521274006289408
  | 55 => 8689127798131301271015662328618014548327600712174592
  | _ => 0

theorem polynomial_n42 : ∀ letter, (∑ word ∈ S_n42.T letter, w_n41 (word 0) * w_Rf (word 1)) = w_n42 letter := by native_decide

theorem step_n42 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n42 base).w letter = w_n42 letter := by
  change (Realisation.multiSubst e_n42 (children_n42 base) S_n42).w letter = w_n42 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n42 base 0).w value = w_n41 value := fun value => step_n41 base correct value
  have child1 : ∀ value, (children_n42 base 1).w value = w_Rf value := fun value => step_Rf base correct value
  simp only [Fin.prod_univ_two, child0, child1]
  exact polynomial_n42 letter

def e_n43 : Fin 2 → Nat := Fin.cases (11) (fun _ => 1)

def children_n43 (base : Realisation Ty typedSep graph) :
    (index : Fin 2) → Realisation Ty typedSep (strongPower graph (e_n43 index)) :=
  Fin.cases (R_n42 base) (fun _ => R_Rf base)

def R_n43 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 12) :=
  Realisation.multiSubst e_n43 (children_n43 base) S_n43

def w_n43 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 1493729980792987470459933626228246220452947140774858101968
  | 2 => 43114404842984133060224749379568895242247797611381101020
  | 3 => 639690911830973465523980495007501573355670644429996264509
  | 5 => 636263626813863481665644824756211645409835855879543962009
  | 7 => 226822731201428768509518709615590784606772905204699902846
  | 9 => 2458435907593160461163532395879352026986174122815777308672
  | 11 => 2349142631193011266447443913547300909811612214235758344
  | 14 => 202840039076240035300186910352552513066366961434624
  | 15 => 628666793060487526935262903270765545409751183732871516408
  | 23 => 486588047653505524578072150064580922751804208513346969600
  | 46 => 37563141478973988006145332114405547597793077381300224
  | 47 => 533822928477713400638647098299855870298821854764194439168
  | 54 => 4125671690265503572238927156778116996962671555520512
  | 55 => 583687329188899195067729422241072164272819303289366849536
  | _ => 0

theorem polynomial_n43 : ∀ letter, (∑ word ∈ S_n43.T letter, w_n42 (word 0) * w_Rf (word 1)) = w_n43 letter := by native_decide

theorem step_n43 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n43 base).w letter = w_n43 letter := by
  change (Realisation.multiSubst e_n43 (children_n43 base) S_n43).w letter = w_n43 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n43 base 0).w value = w_n42 value := fun value => step_n42 base correct value
  have child1 : ∀ value, (children_n43 base 1).w value = w_Rf value := fun value => step_Rf base correct value
  simp only [Fin.prod_univ_two, child0, child1]
  exact polynomial_n43 letter

def e_n44 : Fin 2 → Nat := Fin.cases (12) (fun _ => 1)

def children_n44 (base : Realisation Ty typedSep graph) :
    (index : Fin 2) → Realisation Ty typedSep (strongPower graph (e_n44 index)) :=
  Fin.cases (R_n43 base) (fun _ => R_R1 base)

def R_n44 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 13) :=
  Realisation.multiSubst e_n44 (children_n44 base) S_n44

def w_n44 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 86841868194009149296082879002533659235375083950872385674972464
  | 2 => 3065476330038559027895993033902426639137106329534696170724540
  | 3 => 41151622040332759454312373623558385799777250841239634404049369
  | 5 => 40949480324991903290115377872407227390185130908193701212288467
  | 7 => 16110169514064758151654078459385826043406794101360468645412456
  | 9 => 149380139645672557910359967101926976660373791702986624400580608
  | 11 => 185845833983225478565671147528321659421061428963632287762968
  | 14 => 16455659138119895237982180587123142780461482858015420416
  | 15 => 42159315898012017471123423710791845185582514077111289904891368
  | 23 => 31932404069431855955642343072628937943693638784009716545732608
  | 46 => 2310734211220563846186036250349771666025838948188064579584
  | 47 => 35331505278534482261306836748435596672666305778209383310852096
  | 54 => 287700414064123120965830937603396859814397734916740444160
  | 55 => 38940264385591282908874475395951649038264373102563739766165504
  | _ => 0

theorem polynomial_n44 : ∀ letter, (∑ word ∈ S_n44.T letter, w_n43 (word 0) * w_R1 (word 1)) = w_n44 letter := by native_decide

theorem step_n44 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n44 base).w letter = w_n44 letter := by
  change (Realisation.multiSubst e_n44 (children_n44 base) S_n44).w letter = w_n44 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n44 base 0).w value = w_n43 value := fun value => step_n43 base correct value
  have child1 : ∀ value, (children_n44 base 1).w value = w_R1 value := fun value => step_R1 base correct value
  simp only [Fin.prod_univ_two, child0, child1]
  exact polynomial_n44 letter

def e_n45 : Fin 2 → Nat := Fin.cases (13) (fun _ => 1)

def children_n45 (base : Realisation Ty typedSep graph) :
    (index : Fin 2) → Realisation Ty typedSep (strongPower graph (e_n45 index)) :=
  Fin.cases (R_n44 base) (fun _ => R_R1 base)

def R_n45 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 14) :=
  Realisation.multiSubst e_n45 (children_n45 base) S_n45

def w_n45 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 5048827297002574894112339844234890531470418836856886136739990816656
  | 2 => 215256579147514217866212592299162809085907702028037222034286747292
  | 3 => 2635517081087383579847406906230174974837520285453849234426579393013
  | 5 => 2618203105070552246431890167520781679792719209901752869201020388241
  | 7 => 1129818212774498947186984482817704906948469839364517689092211178574
  | 9 => 9080735219524762641097157243101053706429635550565200338614915743744
  | 11 => 14352437646312206758466772704135577650378084393305862591349773496
  | 14 => 1287328509035550746347750460611968800355279939081223776387072
  | 15 => 2810231700309342694021384450160764422465125370185262263121839106888
  | 23 => 2083445772609478122749378047221549957802971558496984307592102985728
  | 46 => 142147125737444205561980205976516553807245508736736980677689344
  | 47 => 2324924340315039184507656376058118119249359491039156860892566274048
  | 54 => 19749534941885228804707344144735385281840892451395327836266496
  | 55 => 2582747203625399159177237026914200021441989686422546972849640284160
  | _ => 0

theorem polynomial_n45 : ∀ letter, (∑ word ∈ S_n45.T letter, w_n44 (word 0) * w_R1 (word 1)) = w_n45 letter := by native_decide

theorem step_n45 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n45 base).w letter = w_n45 letter := by
  change (Realisation.multiSubst e_n45 (children_n45 base) S_n45).w letter = w_n45 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n45 base 0).w value = w_n44 value := fun value => step_n44 base correct value
  have child1 : ∀ value, (children_n45 base 1).w value = w_R1 value := fun value => step_R1 base correct value
  simp only [Fin.prod_univ_two, child0, child1]
  exact polynomial_n45 letter

def e_n46 : Fin 2 → Nat := Fin.cases (14) (fun _ => 1)

def children_n46 (base : Realisation Ty typedSep graph) :
    (index : Fin 2) → Realisation Ty typedSep (strongPower graph (e_n46 index)) :=
  Fin.cases (R_n45 base) (fun _ => R_R1 base)

def R_n46 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 15) :=
  Realisation.multiSubst e_n46 (children_n46 base) S_n46

def w_n46 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 293533177110315054621768074491961589413301752877086744590183734787438160
  | 2 => 14954175755629266511712513958673807358850208940202558642797836910727036
  | 3 => 168156047055270969221701052546220942819255157823871442951096166055201585
  | 5 => 166464865233835568752836090370841958377167697615772614715914861120682299
  | 7 => 78383610353589833276913771828494939269029746767266942003050225963283912
  | 9 => 552266771872925331543099433458703927007059294143492277194713715109199872
  | 11 => 1086621353732760550217096250736961807416285271820221041644610757809080
  | 14 => 97911977884740513263504845330707017034881811820007063344944857088
  | 15 => 186348576825696117040480111789215021389291221815276226174237676321958984
  | 23 => 135260501647016754700655388057502684005315035680457657721292939406671872
  | 46 => 8744322586864617749350774350851392324006514715449112103368737685504
  | 47 => 152227911231418059792245507074095662682063248899037886598022631478493184
  | 54 => 1339023548551708537582251664304968065882484620953371423156972535808
  | 55 => 170445635797926044798732201930728291511944614308821163496981484460654592
  | _ => 0

theorem polynomial_n46 : ∀ letter, (∑ word ∈ S_n46.T letter, w_n45 (word 0) * w_R1 (word 1)) = w_n46 letter := by native_decide

theorem step_n46 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n46 base).w letter = w_n46 letter := by
  change (Realisation.multiSubst e_n46 (children_n46 base) S_n46).w letter = w_n46 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n46 base 0).w value = w_n45 value := fun value => step_n45 base correct value
  have child1 : ∀ value, (children_n46 base 1).w value = w_R1 value := fun value => step_R1 base correct value
  simp only [Fin.prod_univ_two, child0, child1]
  exact polynomial_n46 letter

def e_n47 : Fin 2 → Nat := Fin.cases (15) (fun _ => 1)

def children_n47 (base : Realisation Ty typedSep graph) :
    (index : Fin 2) → Realisation Ty typedSep (strongPower graph (e_n47 index)) :=
  Fin.cases (R_n46 base) (fun _ => R_R1 base)

def R_n47 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 16) :=
  Realisation.multiSubst e_n47 (children_n47 base) S_n47

def w_n47 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 17065946618537961034689028914262926241404430818527940687631149240910923276880
  | 2 => 1029275411723650141555698008722911047188316360925648105882781597141608064860
  | 3 => 10694906630474805653189929779049528168171696027135431446000013853348447454637
  | 5 => 10532737765952040633868268092279219887557503977056782278074463655905182067945
  | 7 => 5387641326007844815718833537939170035466301308603360363688631976818550653886
  | 9 => 33603303622092414866024449341264929468079478099826042737798636062409780559872
  | 11 => 80906299359747555052111246516182903934174203381032407925379246696442172664
  | 14 => 7281640364214002990576973339803673563449258784380785969577023894847488
  | 15 => 12300876846026992057710950794805998135166455703412144673388946576390209923848
  | 23 => 8743529377326953979083755113782153169674728413000550376529105127103190269952
  | 46 => 537915748253563825469062234966974250203584759235567580150831267461464064
  | 47 => 9924450693991059652364477438697194567534960943534715801039399905151715377152
  | 54 => 89880345837556192338643075385542489738564690458386277516659052374556672
  | 55 => 11199492698182901002085307012074127969831173957305973926484770734691699949568
  | _ => 0

theorem polynomial_n47 : ∀ letter, (∑ word ∈ S_n47.T letter, w_n46 (word 0) * w_R1 (word 1)) = w_n47 letter := by native_decide

theorem step_n47 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n47 base).w letter = w_n47 letter := by
  change (Realisation.multiSubst e_n47 (children_n47 base) S_n47).w letter = w_n47 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n47 base 0).w value = w_n46 value := fun value => step_n46 base correct value
  have child1 : ∀ value, (children_n47 base 1).w value = w_R1 value := fun value => step_R1 base correct value
  simp only [Fin.prod_univ_two, child0, child1]
  exact polynomial_n47 letter

def e_n48 : Fin 2 → Nat := Fin.cases (16) (fun _ => 1)

def children_n48 (base : Realisation Ty typedSep graph) :
    (index : Fin 2) → Realisation Ty typedSep (strongPower graph (e_n48 index)) :=
  Fin.cases (R_n47 base) (fun _ => R_R1 base)

def R_n48 (base : Realisation Ty typedSep graph) : Realisation Ty typedSep (strongPower graph 17) :=
  Realisation.multiSubst e_n48 (children_n48 base) S_n48

def w_n48 (letter : TypeModel.Ty) : Nat :=
  match letter.val with
  | 1 => 992227911602873686733504225763556889434877242708168726677760826825747627987776976
  | 2 => 70269422025807327829579203791757807656163563754523947134449614339559547259084348
  | 3 => 678369869156880684458783632956551753048501868701568533449679260413281995736123433
  | 5 => 663637197032154747392413648947906577036783287995165094511383753474884804538080195
  | 7 => 367328269378764299197153479147475750215351137763592449035735169659976507767965704
  | 9 => 2045622211236840767504552011400162420812317616058711926644862778583628638034591744
  | 11 => 5938678191351227819300312417567129855674360442937829923666435723129734908285368
  | 14 => 531692475994957587967272119445741942530711651097409998133241378793863184384
  | 15 => 808742644916638335693923959151031044402556219152494436654883894237781366396939848
  | 23 => 563074764259837078316674143526090469552293009236582906216891735367280735200346112
  | 46 => 33090425169566232287554832446228387975523720049135175260558536249159423361024
  | 47 => 644586258764355734249001985750939259497113248195705184552867541532596440628592640
  | 54 => 5983387252592938467898212453232603603869075847978152088585848891971352330240
  | 55 => 733085226836598660487905149293712090904332133252198226023704326878681078778232832
  | _ => 0

theorem polynomial_n48 : ∀ letter, (∑ word ∈ S_n48.T letter, w_n47 (word 0) * w_R1 (word 1)) = w_n48 letter := by native_decide

theorem step_n48 (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) (letter : Ty) :
    (R_n48 base).w letter = w_n48 letter := by
  change (Realisation.multiSubst e_n48 (children_n48 base) S_n48).w letter = w_n48 letter
  rw [w_multiSubst]
  have child0 : ∀ value, (children_n48 base 0).w value = w_n47 value := fun value => step_n47 base correct value
  have child1 : ∀ value, (children_n48 base 1).w value = w_R1 value := fun value => step_R1 base correct value
  simp only [Fin.prod_univ_two, child0, child1]
  exact polynomial_n48 letter

def e_terminal : Fin 3 → Nat := Fin.cases (34) (Fin.cases (36) (fun _ => 17))

def children_terminal (base : Realisation Ty typedSep graph) :
    (index : Fin 3) → Realisation Ty typedSep (strongPower graph (e_terminal index)) :=
  Fin.cases (R_n17 base) (Fin.cases (R_n37 base) (fun _ => R_n48 base))

theorem polynomial_terminal : (∑ word ∈ terminalCode.C, w_n17 (word 0) * w_n37 (word 1) * w_n48 (word 2)) = N := by native_decide

theorem step_terminal (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) :
    (∑ word ∈ terminalCode.C, ∏ index, (children_terminal base index).w (word index)) = N := by
  have child0 : ∀ value, (children_terminal base 0).w value = w_n17 value := fun value => step_n17 base correct value
  have child1 : ∀ value, (children_terminal base 1).w value = w_n37 value := fun value => step_n37 base correct value
  have child2 : ∀ value, (children_terminal base 2).w value = w_n48 value := fun value => step_n48 base correct value
  simp only [Fin.prod_univ_three, child0, child1, child2]
  exact polynomial_terminal

def codeBase (base : Realisation Ty typedSep graph) : Finset (Fin 87 → Vertex) :=
  (multiCodeSet e_terminal (children_terminal base) terminalCode).image (strongPower_sum_iso graph e_terminal).symm

theorem independent_codeBase (base : Realisation Ty typedSep graph) :
    (strongPower graph 87).IsIndepSet ↑(codeBase base) :=
  isIndepSet_image_symm (strongPower_sum_iso graph e_terminal)
    (isIndepSet_multiCodeSet e_terminal (children_terminal base) terminalCode)

theorem card_codeBase (base : Realisation Ty typedSep graph) (correct : ∀ letter, base.w letter = TypedBase.w0 letter) :
    (codeBase base).card = N := by
  calc
    (codeBase base).card = (multiCodeSet e_terminal (children_terminal base) terminalCode).card :=
      Finset.card_image_of_injective _ (strongPower_sum_iso graph e_terminal).symm.injective
    _ = ∑ word ∈ terminalCode.C, ∏ index, (children_terminal base index).w (word index) :=
      card_multiCodeSet e_terminal (children_terminal base) terminalCode
    _ = N := step_terminal base correct
end Generic

def code : Finset (Fin 522 → Fin 13) :=
  (codeBase TypedBase.base).image PublicLongCapacity.iso522.symm

theorem card_code : code.card = N := by
  calc
    code.card = (codeBase TypedBase.base).card :=
      Finset.card_image_of_injective _ PublicLongCapacity.iso522.symm.injective
    _ = N := card_codeBase TypedBase.base TypedBase.base_weights

theorem independent_code : (strongPower (cycleGraph 13) 522).IsIndepSet ↑code := by
  rw [← CapC13.Cyc_eq_cycleGraph]
  exact isIndepSet_image_symm PublicLongCapacity.iso522 (independent_codeBase TypedBase.base)

theorem exists_code : ∃ points : Finset (Fin 522 → Fin 13),
    (strongPower (cycleGraph 13) 522).IsIndepSet ↑points ∧ points.card = N :=
  ⟨code, independent_code, card_code⟩

theorem alpha_ge : N ≤ (strongPower (cycleGraph 13) 522).indepNum := by
  rw [← card_code]
  exact SimpleGraph.IsIndepSet.card_le_indepNum independent_code

theorem capacity_root : (N : ℝ) ^ ((1 : ℝ) / (522 : Nat)) ≤ shannonCapacity (cycleGraph 13) := by
  calc
    (N : ℝ) ^ ((1 : ℝ) / (522 : Nat)) ≤
        (((strongPower (cycleGraph 13) 522).indepNum : Nat) : ℝ) ^ ((1 : ℝ) / (522 : Nat)) := by
      apply Real.rpow_le_rpow (by positivity) _ (by positivity)
      exact_mod_cast alpha_ge
    _ ≤ shannonCapacity (cycleGraph 13) := shannonCapacity_ge_root _ 522 (by norm_num)

theorem strictly_larger_public : PublicLong.M < N := by native_decide

theorem strict_root_gt_public :
    (PublicLong.M : ℝ) ^ ((1 : ℝ) / (522 : Nat)) < (N : ℝ) ^ ((1 : ℝ) / (522 : Nat)) := by
  apply Real.rpow_lt_rpow (by positivity) _ (by positivity)
  exact_mod_cast strictly_larger_public

theorem decimal_lower_integer : 6302927403571109 ^ 522 ≤ N * (1000000000000000 : Nat) ^ 522 := by native_decide

theorem capacity_lower : (6.302927403571109 : ℝ) ≤ shannonCapacity (cycleGraph 13) := by
  refine le_trans ?_ capacity_root
  rw [show (6.302927403571109 : ℝ) = (6302927403571109 : ℝ) / 1000000000000000 by norm_num]
  exact Decimal.decimal_le (by norm_num) (by norm_num) decimal_lower_integer le_rfl

theorem capacity_strictly_exceeds_public :
    (PublicLong.M : ℝ) ^ ((1 : ℝ) / (522 : Nat)) < shannonCapacity (cycleGraph 13) :=
  lt_of_lt_of_le strict_root_gt_public capacity_root

end ShannonBounds.ExplorationC13FrontierR03.Capacity
