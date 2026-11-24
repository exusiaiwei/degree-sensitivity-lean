module

public import DegreeSensitivity.IntTrieVerifier

@[expose] public section

/-!
# New World Record: `B_7 ≤ 28` (Impossibility of `(n = 29, d = 7)`)

Small-integer Subset-`J` Terwilliger LP Farkas infeasibility certificate
(361 pure integer multipliers, ≤ 14 digits, `J = [5, 6, 7, 8, 9]`),
verified via `j`-sliced depth-8 `by decide` checks.
Strictly beats Wellens (2022) `B_7 ≤ 29`.
-/

namespace DegreeSensitivity

/-- Balanced binary tree of small-integer Farkas multipliers for `(n = 29, d = 7)`. -/
def cert_29_7 : BinTree BinoStep :=
  (.node
    (.node
      (.node
        (.node
          (.node
            (.node
            (.node
            (.node (.leaf (.eqP0 (-43576909652))) (.leaf (.eqP1 135785427776)))
            (.node (.leaf (.eqDiag 5 31762124617)) (.node (.leaf (.eqB00 5 (-37010575952))) (.leaf (.eqB10 5 6349914207)))))
            (.node
            (.node (.leaf (.eqB01 5 110993987870)) (.node (.leaf (.eqDiag 6 (-46787231933))) (.leaf (.eqB00 6 (-19428674510)))))
            (.node (.leaf (.eqB10 6 24963970350)) (.node (.leaf (.eqB01 6 23310686320)) (.leaf (.eqDiag 7 38310532050))))))
            (.node
            (.node
            (.node (.leaf (.eqB00 7 4784552341)) (.leaf (.eqB10 7 3567591392)))
            (.node (.leaf (.eqB01 7 (-5484779599))) (.node (.leaf (.eqDiag 8 (-18286816507))) (.leaf (.eqB00 8 (-7928961328))))))
            (.node
            (.node (.leaf (.eqB10 8 (-2578983174))) (.node (.leaf (.eqB01 8 15318148482)) (.leaf (.eqDiag 9 4881843151))))
            (.node (.leaf (.eqB00 9 8223548342)) (.node (.leaf (.eqB10 9 (-4431841875))) (.leaf (.eqB01 9 (-14270703991))))))))
          (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 5 6 0 (-20979559286))) (.leaf (.eqSym 5 6 1 552241844450)))
            (.node (.leaf (.eqSym 5 6 2 (-2374975877071))) (.node (.leaf (.eqSym 5 6 3 3325641024591)) (.leaf (.eqSym 5 6 4 (-2129416493307))))))
            (.node
            (.node (.leaf (.eqSym 5 6 5 549876506959)) (.node (.leaf (.eqSym 5 7 0 98127528439)) (.leaf (.eqSym 5 7 1 (-2017636953292)))))
            (.node (.leaf (.eqSym 5 7 2 7367465412317)) (.node (.leaf (.eqSym 5 7 3 (-9913051021942))) (.leaf (.eqSym 5 7 4 6214653315169))))))
            (.node
            (.node
            (.node (.leaf (.eqSym 5 7 5 (-1490548822383))) (.node (.leaf (.eqSym 5 8 0 (-163163214114))) (.leaf (.eqSym 5 8 1 2217599495688))))
            (.node (.leaf (.eqSym 5 8 2 (-7502044205895))) (.node (.leaf (.eqSym 5 8 3 9891760337998)) (.leaf (.eqSym 5 8 4 (-6191151855942))))))
            (.node
            (.node (.leaf (.eqSym 5 8 5 1468607973131)) (.node (.leaf (.eqSym 5 9 0 78153612464)) (.leaf (.eqSym 5 9 1 (-774380365027)))))
            (.node (.leaf (.eqSym 5 9 2 2523780446079)) (.node (.leaf (.eqSym 5 9 3 (-3293704998675))) (.leaf (.eqSym 5 9 4 2083942786336))))))))
        (.node
          (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 5 9 5 (-498931784010))) (.leaf (.eqSym 6 7 0 291720768804)))
            (.node (.leaf (.eqSym 6 7 1 1252693474552)) (.node (.leaf (.eqSym 6 7 2 (-7306903305225))) (.leaf (.eqSym 6 7 3 9538591080002)))))
            (.node
            (.node (.leaf (.eqSym 6 7 4 (-4350309456290))) (.node (.leaf (.eqSym 6 7 5 (-449119590729))) (.leaf (.eqSym 6 7 6 575053560203))))
            (.node (.leaf (.eqSym 6 8 0 (-640068241085))) (.node (.leaf (.eqSym 6 8 2 4917906305933)) (.leaf (.eqSym 6 8 3 (-5641494289189)))))))
            (.node
            (.node
            (.node (.leaf (.eqSym 6 8 4 36930907897)) (.leaf (.eqSym 6 8 5 3199638813550)))
            (.node (.leaf (.eqSym 6 8 6 (-1320226555547))) (.node (.leaf (.eqSym 6 9 0 334492622838)) (.leaf (.eqSym 6 9 1 (-662483149589))))))
            (.node
            (.node (.leaf (.eqSym 6 9 3 (-590407760309))) (.node (.leaf (.eqSym 6 9 4 2192506965799)) (.leaf (.eqSym 6 9 5 (-2206808591689)))))
            (.node (.leaf (.eqSym 6 9 6 700583822116)) (.node (.leaf (.eqSym 7 8 0 914730552220)) (.leaf (.eqSym 7 8 1 (-1948075805301))))))))
          (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 7 8 2 66014538030)) (.leaf (.eqSym 7 8 3 1329052305192)))
            (.node (.leaf (.eqSym 7 8 4 (-511272789491))) (.node (.leaf (.eqSym 7 8 5 159408295491)) (.leaf (.eqSym 7 8 6 (-775106326617))))))
            (.node
            (.node (.leaf (.eqSym 7 8 7 445849167728)) (.node (.leaf (.eqSym 7 9 0 (-525974121042))) (.leaf (.eqSym 7 9 1 1159270744538))))
            (.node (.leaf (.eqSym 7 9 3 (-1703512247131))) (.node (.leaf (.eqSym 7 9 4 2372365430165)) (.leaf (.eqSym 7 9 5 (-2079916805714)))))))
            (.node
            (.node
            (.node (.leaf (.eqSym 7 9 6 1351669352189)) (.node (.leaf (.eqSym 7 9 7 (-409253061618))) (.leaf (.eqSym 8 9 1 1228532825717))))
            (.node (.leaf (.eqSym 8 9 2 (-5877295777499))) (.node (.leaf (.eqSym 8 9 3 12323674262667)) (.leaf (.eqSym 8 9 4 (-15095022631825))))))
            (.node
            (.node (.leaf (.eqSym 8 9 5 11571278197603)) (.node (.leaf (.eqSym 8 9 6 (-5469630078775))) (.leaf (.eqSym 8 9 7 1408801473731))))
            (.node (.leaf (.eqSym 8 9 8 (-135146140035))) (.node (.leaf (.ubPHi 2 74019588480)) (.leaf (.ubPHi 29 2211297527)))))))))
      (.node
        (.node
          (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePj 5 0 2 82854579276)) (.leaf (.ubHGe0 5 0 17 1694399711)))
            (.node (.leaf (.ubHLePj 5 0 22 719637296)) (.node (.leaf (.ubHGe0 5 0 24 34772447)) (.leaf (.ubHLePj 5 1 1 29050542149)))))
            (.node
            (.node (.leaf (.ubHGe0 5 1 24 524649760)) (.node (.leaf (.ubHMcc 5 2 0 14512285054)) (.leaf (.ubHGe0 5 2 16 255548310))))
            (.node (.leaf (.ubHLePj 5 2 23 542057934)) (.node (.leaf (.ubHGe0 5 3 2 10645637419)) (.leaf (.ubHLePj 5 4 0 25445279870))))))
            (.node
            (.node
            (.node (.leaf (.ubHGe0 5 4 13 4704387668)) (.leaf (.ubHLePj 5 4 19 1849401143)))
            (.node (.leaf (.ubHGe0 5 4 23 618045602)) (.node (.leaf (.ubHLePj 5 5 7 2738788729)) (.leaf (.ubHGe0 5 5 13 818377246)))))
            (.node
            (.node (.leaf (.ubHLePj 5 5 18 1751212665)) (.node (.leaf (.ubHGe0 5 5 23 2990867043)) (.leaf (.ubHLePj 5 5 24 2077493816))))
            (.node (.leaf (.ubHGe0 6 0 6 3750845764)) (.node (.leaf (.ubHLePj 6 0 19 673502792)) (.leaf (.ubHGe0 6 0 23 165853923)))))))
          (.node
            (.node
            (.node
            (.node (.leaf (.ubHGe0 6 1 5 23606427104)) (.leaf (.ubHLePj 6 1 11 8915239072)))
            (.node (.leaf (.ubHLePj 6 1 12 2377941642)) (.node (.leaf (.ubHGe0 6 1 23 691263773)) (.leaf (.ubHLePj 6 2 0 20136681014)))))
            (.node
            (.node (.leaf (.ubHGe0 6 2 16 6115558793)) (.node (.leaf (.ubHLePj 6 3 8 12112094882)) (.leaf (.ubHLePj 6 3 21 3689351892))))
            (.node (.leaf (.ubHLePj 6 3 23 3150547312)) (.node (.leaf (.ubHGe0 6 4 14 403948989)) (.leaf (.ubHGe0 6 4 22 4150820475))))))
            (.node
            (.node
            (.node (.leaf (.ubHGe0 6 4 23 3990141249)) (.node (.leaf (.ubHLePj 6 5 18 3051607291)) (.leaf (.ubHLePi 6 5 23 3114268536))))
            (.node (.leaf (.ubHGe0 6 6 11 968029418)) (.node (.leaf (.ubHGe0 6 6 21 1293540881)) (.leaf (.ubHLePj 6 6 23 63511593)))))
            (.node
            (.node (.leaf (.ubHLePj 7 0 12 391638808)) (.node (.leaf (.ubHLePj 7 1 1 24359900652)) (.leaf (.ubHLePi 7 1 17 1939258323))))
            (.node (.leaf (.ubHLePj 7 1 22 1130014439)) (.node (.leaf (.ubHGe0 7 2 16 2497345867)) (.leaf (.ubHMcc 7 2 21 2955085071))))))))
        (.node
          (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePj 7 4 19 2242801422)) (.leaf (.ubHLePj 7 4 20 1008416783)))
            (.node (.leaf (.ubHGe0 7 5 0 16775898621)) (.node (.leaf (.ubHGe0 7 5 13 2831220553)) (.leaf (.ubHLePi 7 5 22 447214594)))))
            (.node
            (.node (.leaf (.ubHGe0 7 6 21 1509465369)) (.node (.leaf (.ubHLePj 7 7 4 677338637)) (.leaf (.ubHLePi 7 7 11 373307161))))
            (.node (.leaf (.ubHLePj 7 7 16 343576597)) (.node (.leaf (.ubHLePj 7 7 22 320203545)) (.leaf (.ubHGe0 8 0 18 1533557173))))))
            (.node
            (.node
            (.node (.leaf (.ubHLePi 8 1 17 1786612273)) (.leaf (.ubHMcc 8 2 0 13329019480)))
            (.node (.leaf (.ubHLePj 8 2 21 689877332)) (.node (.leaf (.ubHMcc 8 3 20 340326050)) (.leaf (.ubHMcc 8 3 21 392467185)))))
            (.node
            (.node (.leaf (.ubHLePi 8 6 0 2641428228)) (.node (.leaf (.ubHGe0 8 6 21 155789332)) (.leaf (.ubHLePi 8 7 20 536073859))))
            (.node (.leaf (.ubHGe0 8 7 21 113649086)) (.node (.leaf (.ubHMcc 8 8 4 4382583367)) (.leaf (.ubHLePi 8 8 10 1492987997)))))))
          (.node
            (.node
            (.node
            (.node (.leaf (.ubHMcc 8 8 15 643297307)) (.leaf (.ubHMcc 8 8 21 29625142)))
            (.node (.leaf (.ubHMcc 9 0 11 905894840)) (.node (.leaf (.ubHLePi 9 0 17 1228855981)) (.leaf (.ubHGe0 9 0 20 87283657)))))
            (.node
            (.node (.leaf (.ubHMcc 9 1 1 9463271602)) (.node (.leaf (.ubHMcc 9 1 11 976422214)) (.leaf (.ubHGe0 9 1 17 1176945067))))
            (.node (.leaf (.ubHMcc 9 1 20 86622519)) (.node (.leaf (.ubHLePj 9 2 0 6190590480)) (.leaf (.ubHLePi 9 3 15 728722565))))))
            (.node
            (.node
            (.node (.leaf (.ubHLePj 9 4 19 783425784)) (.node (.leaf (.ubHMcc 9 5 6 4179888172)) (.leaf (.ubHMcc 9 5 18 1200045276))))
            (.node (.leaf (.ubHLePi 9 6 0 4513196465)) (.node (.leaf (.ubHLePi 9 6 12 1518527301)) (.leaf (.ubHMcc 9 6 17 67945591)))))
            (.node
            (.node (.leaf (.ubHLePj 9 7 4 5340526342)) (.node (.leaf (.ubHLePi 9 7 11 201857688)) (.leaf (.ubHMcc 9 8 3 4142651876))))
            (.node (.leaf (.ubHGe0 9 8 10 459239932)) (.node (.leaf (.ubHMcc 9 8 15 682301404)) (.leaf (.ubHLePi 9 8 20 354565508))))))))))
    (.node
      (.node
        (.node
          (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePj 9 9 2 3696253514)) (.leaf (.ubHMcc 9 9 3 241766248)))
            (.node (.leaf (.ubHLePi 9 9 18 112491276)) (.node (.leaf (.ubHLePi 9 9 19 659927370)) (.leaf (.ubHMcc 9 9 20 670786944)))))
            (.node
            (.node (.leaf (.ubHGe0 5 0 7 266336)) (.node (.leaf (.ubHGe0 5 1 6 327321)) (.leaf (.ubHGe0 5 2 5 173732))))
            (.node (.leaf (.ubHGe0 5 3 4 44287)) (.node (.leaf (.ubHGe0 5 4 3 4743)) (.leaf (.ubHGe0 5 5 2 153))))))
            (.node
            (.node
            (.node (.leaf (.ubHLePi 5 0 6 2082457)) (.leaf (.ubHLePi 5 1 5 2203744)))
            (.node (.leaf (.ubHLePi 5 2 4 955812)) (.node (.leaf (.ubHLePi 5 3 3 187055)) (.leaf (.ubHLePi 5 4 2 14278)))))
            (.node
            (.node (.leaf (.ubHLePi 5 5 1 290)) (.node (.leaf (.ubHGe0 5 0 5 7004007)) (.leaf (.ubHGe0 5 1 4 6178399))))
            (.node (.leaf (.ubHGe0 5 2 3 2096403)) (.node (.leaf (.ubHGe0 5 4 1 14319)) (.leaf (.ubHGe0 5 5 0 138)))))))
          (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 5 0 4 13122083)) (.leaf (.ubHLePi 5 1 3 9227193)))
            (.node (.leaf (.ubHLePi 5 2 2 2291577)) (.node (.leaf (.ubHLePi 5 3 1 206876)) (.leaf (.ubHLePi 5 4 0 4785)))))
            (.node
            (.node (.leaf (.ubHGe0 5 0 3 14776832)) (.node (.leaf (.ubHGe0 5 1 2 7738862)) (.leaf (.ubHGe0 5 2 1 1248539))))
            (.node (.leaf (.ubHGe0 5 3 0 54197)) (.node (.leaf (.ubHLePi 5 0 2 9994244)) (.leaf (.ubHLePi 5 1 1 3454940))))))
            (.node
            (.node
            (.node (.leaf (.ubHLePi 5 2 0 271285)) (.node (.leaf (.ubHGe0 5 0 1 3756679)) (.leaf (.ubHGe0 5 1 0 641296))))
            (.node (.leaf (.ubHLePi 5 0 0 605071)) (.node (.leaf (.ubHLePi 6 0 7 74616)) (.leaf (.ubHLePi 6 1 6 8278)))))
            (.node
            (.node (.leaf (.ubHGe0 6 2 5 32004)) (.node (.leaf (.ubHGe0 6 3 4 6384)) (.leaf (.ubHLePi 6 4 3 372))))
            (.node (.leaf (.ubHLePi 6 5 2 102)) (.node (.leaf (.ubHLePi 6 6 1 3)) (.leaf (.ubHLePi 6 1 5 23860))))))))
        (.node
          (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 6 2 4 175778)) (.leaf (.ubHLePi 6 3 3 24114)))
            (.node (.leaf (.ubHGe0 6 4 2 1447)) (.node (.leaf (.ubHGe0 6 5 1 206)) (.leaf (.ubHGe0 6 6 0 2)))))
            (.node
            (.node (.leaf (.ubHLePi 6 0 5 1395814)) (.node (.leaf (.ubHGe0 6 1 4 250922)) (.leaf (.ubHGe0 6 2 3 380388))))
            (.node (.leaf (.ubHGe0 6 3 2 33486)) (.node (.leaf (.ubHLePi 6 4 1 1781)) (.leaf (.ubHLePi 6 5 0 104))))))
            (.node
            (.node
            (.node (.leaf (.ubHGe0 6 0 4 2106518)) (.leaf (.ubHLePi 6 1 3 598561)))
            (.node (.leaf (.ubHLePi 6 2 2 406188)) (.node (.leaf (.ubHLePi 6 3 1 20175)) (.leaf (.ubHGe0 6 4 0 706)))))
            (.node
            (.node (.leaf (.ubHLePi 6 0 3 1833604)) (.node (.leaf (.ubHGe0 6 1 2 652712)) (.leaf (.ubHGe0 6 2 1 214302))))
            (.node (.leaf (.ubHGe0 6 3 0 4418)) (.node (.leaf (.ubHGe0 6 0 2 903935)) (.leaf (.ubHLePi 6 1 1 344464)))))))
          (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 6 2 0 44728)) (.leaf (.ubHLePi 6 0 1 224913)))
            (.node (.leaf (.ubHGe0 6 1 0 71529)) (.node (.leaf (.ubHGe0 6 0 0 19632)) (.leaf (.ubHLePi 7 0 7 52599)))))
            (.node
            (.node (.leaf (.ubHLePi 7 1 6 73970)) (.node (.leaf (.ubHGe0 7 2 5 11844)) (.leaf (.ubHGe0 7 3 4 35639))))
            (.node (.leaf (.ubHGe0 7 4 3 12349)) (.node (.leaf (.ubHGe0 7 5 2 1503)) (.leaf (.ubHGe0 7 6 1 55))))))
            (.node
            (.node
            (.node (.leaf (.ubHGe0 7 0 6 415099)) (.node (.leaf (.ubHGe0 7 1 5 390392)) (.leaf (.ubHLePi 7 2 4 163849))))
            (.node (.leaf (.ubHLePi 7 3 3 184353)) (.node (.leaf (.ubHLePi 7 4 2 42601)) (.leaf (.ubHLePi 7 5 1 3194)))))
            (.node
            (.node (.leaf (.ubHLePi 7 6 0 55)) (.node (.leaf (.ubHLePi 7 0 5 1355549)) (.leaf (.ubHLePi 7 1 4 749149))))
            (.node (.leaf (.ubHGe0 7 2 3 588772)) (.node (.leaf (.ubHGe0 7 3 2 347686)) (.leaf (.ubHGe0 7 4 1 48460)))))))))
      (.node
        (.node
          (.node
            (.node
            (.node
            (.node (.leaf (.ubHGe0 7 0 4 2364403)) (.leaf (.ubHGe0 7 1 3 542466)))
            (.node (.leaf (.ubHLePi 7 2 2 908559)) (.node (.leaf (.ubHLePi 7 3 1 285172)) (.leaf (.ubHLePi 7 4 0 18208)))))
            (.node
            (.node (.leaf (.ubHLePi 7 0 3 2356728)) (.node (.leaf (.ubHGe0 7 1 2 75988)) (.leaf (.ubHGe0 7 2 1 647157))))
            (.node (.leaf (.ubHGe0 7 3 0 86201)) (.node (.leaf (.ubHGe0 7 0 2 1316852)) (.leaf (.ubHLePi 7 1 1 290983))))))
            (.node
            (.node
            (.node (.leaf (.ubHLePi 7 2 0 175365)) (.leaf (.ubHLePi 7 0 1 365777)))
            (.node (.leaf (.ubHGe0 7 1 0 105255)) (.node (.leaf (.ubHGe0 7 0 0 34300)) (.leaf (.ubHLePi 8 0 7 33096)))))
            (.node
            (.node (.leaf (.ubHLePi 8 1 6 114344)) (.node (.leaf (.ubHLePi 8 2 5 158118)) (.leaf (.ubHLePi 8 3 4 94089))))
            (.node (.leaf (.ubHLePi 8 4 3 27034)) (.node (.leaf (.ubHLePi 8 5 2 3594)) (.leaf (.ubHLePi 8 6 1 188)))))))
          (.node
            (.node
            (.node
            (.node (.leaf (.ubHGe0 8 0 6 329831)) (.leaf (.ubHGe0 8 1 5 960077)))
            (.node (.leaf (.ubHGe0 8 2 4 1026552)) (.node (.leaf (.ubHGe0 8 3 3 463499)) (.leaf (.ubHGe0 8 4 2 94753)))))
            (.node
            (.node (.leaf (.ubHGe0 8 5 1 7952)) (.node (.leaf (.ubHGe0 8 6 0 189)) (.leaf (.ubHLePi 8 0 5 1406253))))
            (.node (.leaf (.ubHLePi 8 1 4 3287133)) (.node (.leaf (.ubHLePi 8 2 3 2634585)) (.leaf (.ubHLePi 8 3 2 847998))))))
            (.node
            (.node
            (.node (.leaf (.ubHLePi 8 4 1 109848)) (.node (.leaf (.ubHLePi 8 5 0 4359)) (.leaf (.ubHGe0 8 0 4 3300208))))
            (.node (.leaf (.ubHGe0 8 1 3 5897762)) (.node (.leaf (.ubHGe0 8 2 2 3344082)) (.leaf (.ubHGe0 8 3 1 683395)))))
            (.node
            (.node (.leaf (.ubHGe0 8 4 0 42130)) (.node (.leaf (.ubHLePi 8 0 3 4590708)) (.leaf (.ubHLePi 8 1 2 5863982))))
            (.node (.leaf (.ubHLePi 8 2 1 2100989)) (.node (.leaf (.ubHLePi 8 3 0 204808)) (.leaf (.ubHGe0 8 0 2 3782274))))))))
        (.node
          (.node
            (.node
            (.node
            (.node (.leaf (.ubHGe0 8 1 1 3069228)) (.leaf (.ubHGe0 8 2 0 523059)))
            (.node (.leaf (.ubHLePi 8 0 1 1709365)) (.node (.leaf (.ubHLePi 8 1 0 661607)) (.leaf (.ubHGe0 8 0 0 327108)))))
            (.node
            (.node (.leaf (.ubHGe0 9 0 7 53348)) (.node (.leaf (.ubHGe0 9 1 6 64924)) (.leaf (.ubHGe0 9 2 5 16866))))
            (.node (.leaf (.ubHLePi 9 3 4 30793)) (.node (.leaf (.ubHLePi 9 4 3 24816)) (.leaf (.ubHLePi 9 5 2 6381))))))
            (.node
            (.node
            (.node (.leaf (.ubHLePi 9 6 1 615)) (.node (.leaf (.ubHLePi 9 7 0 23)) (.leaf (.ubHLePi 9 0 6 410361))))
            (.node (.leaf (.ubHLePi 9 1 5 394020)) (.node (.leaf (.ubHGe0 9 2 4 16338)) (.leaf (.ubHGe0 9 3 3 216384)))))
            (.node
            (.node (.leaf (.ubHGe0 9 4 2 102401)) (.node (.leaf (.ubHGe0 9 5 1 15785)) (.leaf (.ubHGe0 9 6 0 736))))
            (.node (.leaf (.ubHGe0 9 0 5 1341364)) (.node (.leaf (.ubHGe0 9 1 4 898028)) (.leaf (.ubHLePi 9 2 3 361473)))))))
          (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 9 3 2 512919)) (.leaf (.ubHLePi 9 4 1 136580)))
            (.node (.leaf (.ubHLePi 9 5 0 9680)) (.node (.leaf (.ubHLePi 9 0 4 2386229)) (.leaf (.ubHLePi 9 1 3 872714)))))
            (.node
            (.node (.leaf (.ubHGe0 9 2 2 860356)) (.node (.leaf (.ubHGe0 9 3 1 506896)) (.leaf (.ubHGe0 9 4 0 59366))))
            (.node (.leaf (.ubHGe0 9 0 3 2453747)) (.node (.leaf (.ubHGe0 9 1 2 177417)) (.leaf (.ubHLePi 9 2 1 790553))))))
            (.node
            (.node
            (.node (.leaf (.ubHLePi 9 3 0 179879)) (.node (.leaf (.ubHLePi 9 0 2 1418979)) (.leaf (.ubHGe0 9 1 1 253374))))
            (.node (.leaf (.ubHGe0 9 2 0 258626)) (.node (.leaf (.ubHGe0 9 0 1 403302)) (.leaf (.ubHLePi 9 1 0 127056)))))
            (.node
            (.node (.leaf (.ubHLePi 9 0 0 36186)) (.node (.leaf (.ubPHi 7 520023)) (.leaf (.ubPHi 6 8100099))))
            (.node (.leaf (.ubPHi 5 9242455)) (.node (.leaf (.ubPHi 4 36092741)) (.leaf (.ubPHi 3 12371194)))))))))))

private lemma cert_29_7_u : checkBinoFarkasU 29 7 cert_29_7 = true := by decide
private lemma cert_29_7_c_5 : checkBinoCForJ 29 7 5 cert_29_7 = true := by decide
private lemma cert_29_7_c_6 : checkBinoCForJ 29 7 6 cert_29_7 = true := by decide
private lemma cert_29_7_c_7 : checkBinoCForJ 29 7 7 cert_29_7 = true := by decide
private lemma cert_29_7_c_8 : checkBinoCForJ 29 7 8 cert_29_7 = true := by decide
private lemma cert_29_7_c_9 : checkBinoCForJ 29 7 9 cert_29_7 = true := by decide
private lemma cert_29_7_c_rest :
    ([0, 1, 2, 3, 4, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29] : List ℕ).all (fun j => checkBinoCForJ 29 7 j cert_29_7) = true := by
  decide
lemma cert_29_7_c_ok : ∀ j ≤ 29, checkBinoCForJ 29 7 j cert_29_7 = true := by
  have hcov : ∀ j : Fin 30, j.val = 5 ∨ j.val = 6 ∨ j.val = 7 ∨ j.val = 8 ∨ j.val = 9 ∨ j.val ∈ ([0, 1, 2, 3, 4, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29] : List ℕ) := by decide
  intro j hj
  rcases hcov ⟨j, by omega⟩ with h | h | h | h | h | h
  · dsimp only at h; rw [h]; exact cert_29_7_c_5
  · dsimp only at h; rw [h]; exact cert_29_7_c_6
  · dsimp only at h; rw [h]; exact cert_29_7_c_7
  · dsimp only at h; rw [h]; exact cert_29_7_c_8
  · dsimp only at h; rw [h]; exact cert_29_7_c_9
  · exact List.all_eq_true.mp cert_29_7_c_rest j h

/-- **World Record `B_7 ≤ 28`**: Every Boolean function of polynomial degree `≤ 7` has
maximum sensitivity `≤ 28` (kernel-verified via `j`-sliced `by decide`). -/
theorem maxSensitivity_le_twentyeight_of_deg_le_seven_proof {m : ℕ} (f : BooleanFun m) (hf : polyDegree f ≤ 7) :
    maxSensitivity f ≤ 28 := by
  have hlt := maxSensitivity_lt_of_bino_farkas_sliced (n := 29) (d := 7) cert_29_7 cert_29_7_u cert_29_7_c_ok f hf
  omega

end DegreeSensitivity
