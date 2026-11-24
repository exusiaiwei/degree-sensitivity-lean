module

public import DegreeSensitivity.IntTrieVerifier

@[expose] public section

/-!
# Small-Integer Step 1 & Step 2 LP Certificates for `B_6 ≤ 20` (`(21, 6)` Impossibility)

Unit-triangular small-integer balanced `BinTree BinoStep` certificates (≤ 14 digits) verified
via `j`-sliced depth-8 `by decide` checks (minimal kernel memory footprint):
- `step1a`: `S_2 > 209` (`S_2 = 210`, `p_2 = 1`)
- `step1b`: `S_20 > 20` (`S_20 = 21`, `p_20 = 1`)
- `step1c`: `S_21 < 1` (`S_21 = 0`, `p_21 = 0`)
- `step2a`: `S_19 > 209` (`S_19 = 210`, `p_19 = 1`)
- `step2b`: `S_3 > 838` (`S_3 ≥ 839`)
- `step2c`: `S_3 < 843` (`S_3 ≤ 842`)
-/

namespace DegreeSensitivity

def step1aScale : ℕ := 10000000000
def step1aLb : ℤ := 9956582263
def step1aCert : BinTree BinoStep :=
  (.node
    (.node
      (.node
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.eqP0 (-15277544505))) (.node (.leaf (.eqP1 43630558481)) (.leaf (.eqB00 0 (-1307639547)))))
            (.node (.node (.leaf (.eqB01 0 3275483826)) (.leaf (.eqB00 2 (-3016955686)))) (.node (.leaf (.eqB10 2 5041867625)) (.leaf (.eqB01 2 4816083593)))))
            (.node
            (.node (.node (.leaf (.eqDiag 3 420362773)) (.leaf (.eqDiag 4 550849423))) (.node (.leaf (.eqB00 4 (-3159237371))) (.leaf (.eqB10 4 4964769828))))
            (.node (.node (.leaf (.eqB01 4 5279251503)) (.leaf (.eqDiag 5 164446407))) (.node (.leaf (.eqB00 6 (-517265380))) (.leaf (.eqB10 6 1139105510))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqB00 7 (-1981157160))) (.leaf (.eqB10 7 2093345117))) (.node (.leaf (.eqB01 7 2445740858)) (.leaf (.eqDiag 8 3550897743))))
            (.node (.node (.leaf (.eqB00 9 (-4697032507))) (.leaf (.eqB10 9 421675398))) (.node (.leaf (.eqB01 9 13023150632)) (.leaf (.eqDiag 10 2702857044)))))
            (.node
            (.node (.node (.leaf (.eqB10 10 6123099018)) (.leaf (.eqB00 11 (-5507078415)))) (.node (.leaf (.eqB10 11 8787505295)) (.leaf (.eqB01 11 5092312446))))
            (.node (.node (.leaf (.eqDiag 12 957307342)) (.leaf (.eqDiag 13 470415772))) (.node (.leaf (.eqB00 13 (-46130988))) (.leaf (.eqB01 13 533741532)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.eqDiag 14 567241621)) (.node (.leaf (.eqB01 14 6484435876)) (.leaf (.eqB00 15 (-465482976)))))
            (.node (.node (.leaf (.eqB10 15 886300213)) (.leaf (.eqB01 15 1311225082))) (.node (.leaf (.eqDiag 16 459130126)) (.leaf (.eqB00 16 (-1793761619))))))
            (.node
            (.node (.node (.leaf (.eqB10 16 2887728389)) (.leaf (.eqB01 16 2113758762))) (.node (.leaf (.eqB10 17 2987591077)) (.leaf (.eqDiag 18 283570666))))
            (.node (.node (.leaf (.eqB00 19 (-778500158))) (.leaf (.eqDiag 20 117211727))) (.node (.leaf (.eqDiag 21 26831405)) (.leaf (.eqB00 21 (-411855913)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 0 3 0 4245997552)) (.leaf (.eqSym 0 5 0 (-2947935443)))) (.node (.leaf (.eqSym 0 9 0 849199510)) (.leaf (.eqSym 0 15 0 (-291154118)))))
            (.node (.node (.leaf (.eqSym 0 19 0 172393886)) (.leaf (.eqSym 0 21 0 (-60657108)))) (.node (.leaf (.eqSym 1 2 1 (-3075243657))) (.leaf (.eqSym 1 3 0 (-6722727255))))))
            (.node
            (.node (.node (.leaf (.eqSym 1 8 1 4465401254)) (.leaf (.eqSym 1 11 0 5079393926))) (.node (.leaf (.eqSym 1 11 1 (-4966518506))) (.leaf (.eqSym 1 14 0 (-5358481504)))))
            (.node (.node (.leaf (.eqSym 1 19 0 4411052620)) (.leaf (.eqSym 1 19 1 17927272680))) (.node (.leaf (.eqSym 1 20 0 (-2767719291))) (.leaf (.eqSym 1 20 1 (-26139571082)))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 1 21 1 10354282542)) (.node (.leaf (.eqSym 2 3 0 1147982928)) (.leaf (.eqSym 2 3 1 6517832549))))
            (.node (.node (.leaf (.eqSym 2 3 2 759122911)) (.leaf (.eqSym 2 4 1 (-6602499096)))) (.node (.leaf (.eqSym 2 4 2 828004144)) (.leaf (.eqSym 2 5 0 (-5774896))))))
            (.node
            (.node (.node (.leaf (.eqSym 2 5 1 7533855056)) (.leaf (.eqSym 2 5 2 902900651))) (.node (.leaf (.eqSym 2 6 0 1294394746)) (.leaf (.eqSym 2 6 1 (-699335388)))))
            (.node (.node (.leaf (.eqSym 2 6 2 (-66109793))) (.leaf (.eqSym 2 7 1 (-1750893223)))) (.node (.leaf (.eqSym 2 8 0 148244918)) (.leaf (.eqSym 2 9 1 (-9876330819)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 2 9 2 1842147493)) (.leaf (.eqSym 2 12 1 11027237191))) (.node (.leaf (.eqSym 2 13 1 (-353763804))) (.leaf (.eqSym 2 14 0 (-2893153365)))))
            (.node (.node (.leaf (.eqSym 2 15 1 (-1262438980))) (.leaf (.eqSym 2 16 1 (-4810834251)))) (.node (.leaf (.eqSym 2 17 0 3634109871)) (.leaf (.eqSym 2 17 1 6462921963)))))
            (.node
            (.node (.node (.leaf (.eqSym 2 17 2 (-5517337964))) (.leaf (.eqSym 2 19 0 (-1436771114)))) (.node (.leaf (.eqSym 2 19 1 (-9221741165))) (.leaf (.eqSym 2 19 2 6591804948))))
            (.node (.node (.leaf (.eqSym 2 20 1 7795260662)) (.leaf (.eqSym 2 21 2 (-2390955688)))) (.node (.leaf (.eqSym 3 4 0 (-2198017676))) (.leaf (.eqSym 3 4 2 (-6200347058))))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 3 5 0 2370978249)) (.leaf (.eqSym 3 5 1 (-2737552193)))) (.node (.leaf (.eqSym 3 5 2 9407667976)) (.leaf (.eqSym 3 5 3 (-1898857916)))))
            (.node (.node (.leaf (.eqSym 3 8 2 2164232924)) (.leaf (.eqSym 3 8 3 (-4500873854)))) (.node (.leaf (.eqSym 3 9 0 (-14482638562))) (.leaf (.eqSym 3 9 1 6165836933)))))
            (.node
            (.node (.node (.leaf (.eqSym 3 10 0 21926612663)) (.leaf (.eqSym 3 10 3 (-326188090)))) (.node (.leaf (.eqSym 3 11 0 (-10330099225))) (.leaf (.eqSym 3 11 2 (-8077128654)))))
            (.node (.node (.leaf (.eqSym 3 12 3 4250538806)) (.leaf (.eqSym 3 13 1 (-1226980201)))) (.node (.leaf (.eqSym 3 14 0 2083341525)) (.leaf (.eqSym 3 15 1 (-772219892)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 3 16 2 3374320578)) (.leaf (.eqSym 3 17 0 (-732662848)))) (.node (.leaf (.eqSym 3 17 1 (-3192760252))) (.leaf (.eqSym 3 18 0 (-16104270)))))
            (.node (.node (.leaf (.eqSym 3 18 1 270255173)) (.leaf (.eqSym 3 18 2 73649926))) (.node (.leaf (.eqSym 3 19 1 2231445157)) (.leaf (.eqSym 3 19 2 4833526316)))))
            (.node
            (.node (.node (.leaf (.eqSym 3 19 3 (-4061470079))) (.leaf (.eqSym 3 20 2 (-4816799097)))) (.node (.leaf (.eqSym 3 20 3 1618572190)) (.leaf (.eqSym 3 21 3 1070066442))))
            (.node (.node (.leaf (.eqSym 4 5 2 (-12709681792))) (.leaf (.eqSym 4 7 4 (-1592302656)))) (.node (.leaf (.eqSym 4 8 2 12123255314)) (.leaf (.eqSym 4 8 4 5920828524)))))))))
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 4 9 1 (-4255516995))) (.node (.leaf (.eqSym 4 9 4 (-6027921142))) (.leaf (.eqSym 4 10 0 234044971))))
            (.node (.node (.leaf (.eqSym 4 10 4 1165784911)) (.leaf (.eqSym 4 11 2 (-5056508737)))) (.node (.leaf (.eqSym 4 13 1 3610741693)) (.leaf (.eqSym 4 13 4 606878839)))))
            (.node
            (.node (.node (.leaf (.eqSym 4 14 0 (-170578857))) (.leaf (.eqSym 4 14 4 (-208454541)))) (.node (.leaf (.eqSym 4 15 0 (-568918478))) (.leaf (.eqSym 4 17 0 427448819))))
            (.node (.node (.leaf (.eqSym 4 17 1 (-992953966))) (.leaf (.eqSym 4 17 2 (-48837978)))) (.node (.leaf (.eqSym 4 19 2 319430278)) (.leaf (.eqSym 4 19 4 260504737))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 4 20 4 (-231465056))) (.leaf (.eqSym 5 6 1 (-2625922715)))) (.node (.leaf (.eqSym 5 6 3 (-2477101667))) (.leaf (.eqSym 5 6 5 (-263125595)))))
            (.node (.node (.leaf (.eqSym 5 8 0 1597092697)) (.leaf (.eqSym 5 8 1 3326348247))) (.node (.leaf (.eqSym 5 8 4 (-1803375681))) (.leaf (.eqSym 5 8 5 (-1595350810))))))
            (.node
            (.node (.node (.leaf (.eqSym 5 9 0 5628807194)) (.leaf (.eqSym 5 9 2 131476789))) (.node (.leaf (.eqSym 5 9 5 9658172981)) (.leaf (.eqSym 5 10 0 (-10039871069)))))
            (.node (.node (.leaf (.eqSym 5 10 1 (-10732123304))) (.leaf (.eqSym 5 10 3 (-5223497226)))) (.node (.leaf (.eqSym 5 10 5 (-10964390469))) (.leaf (.eqSym 5 11 0 2187174906)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 5 11 1 13501907708)) (.node (.leaf (.eqSym 5 11 2 (-4035020911))) (.leaf (.eqSym 5 11 3 5446844272))))
            (.node (.node (.leaf (.eqSym 5 11 4 3850220547)) (.leaf (.eqSym 5 11 5 3070466143))) (.node (.leaf (.eqSym 5 12 0 1463360538)) (.leaf (.eqSym 5 12 1 1614611203)))))
            (.node
            (.node (.node (.leaf (.eqSym 5 12 3 751045125)) (.leaf (.eqSym 5 13 1 (-5940229003)))) (.node (.leaf (.eqSym 5 13 4 (-566581608))) (.leaf (.eqSym 5 15 1 590482205))))
            (.node (.node (.leaf (.eqSym 5 15 2 1562580082)) (.leaf (.eqSym 5 16 1 (-159969963)))) (.node (.leaf (.eqSym 5 16 4 (-2521714078))) (.leaf (.eqSym 5 16 5 (-2251426165)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 5 17 5 3476229824)) (.leaf (.eqSym 5 18 2 (-87570485)))) (.node (.leaf (.eqSym 5 19 3 (-396148420))) (.leaf (.eqSym 5 19 4 1041450820))))
            (.node (.node (.leaf (.eqSym 5 19 5 (-1042081434))) (.leaf (.eqSym 6 7 1 (-4883716348)))) (.node (.leaf (.eqSym 6 7 5 (-4714612328))) (.leaf (.eqSym 6 8 3 (-19216481090))))))
            (.node
            (.node (.node (.leaf (.eqSym 6 8 5 5083969869)) (.leaf (.eqSym 6 9 0 506366243))) (.node (.leaf (.eqSym 6 9 1 9467063685)) (.leaf (.eqSym 6 9 3 21561063457))))
            (.node (.node (.leaf (.eqSym 6 9 5 1594281816)) (.leaf (.eqSym 6 9 6 (-229838229)))) (.node (.leaf (.eqSym 6 10 1 (-8510964308))) (.leaf (.eqSym 6 11 2 1253442069))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 6 11 3 (-2793742492))) (.node (.leaf (.eqSym 6 11 5 (-2377486164))) (.leaf (.eqSym 6 12 0 (-51153165)))))
            (.node (.node (.leaf (.eqSym 6 12 3 (-6352742970))) (.leaf (.eqSym 6 13 0 (-232832102)))) (.node (.leaf (.eqSym 6 13 1 1805614781)) (.leaf (.eqSym 6 13 4 758940621)))))
            (.node
            (.node (.node (.leaf (.eqSym 6 13 6 (-168543960))) (.leaf (.eqSym 6 14 0 21589631))) (.node (.leaf (.eqSym 6 14 2 (-1319551862))) (.leaf (.eqSym 6 14 3 5123070207))))
            (.node (.node (.leaf (.eqSym 6 15 1 (-77777291))) (.leaf (.eqSym 6 15 3 (-1381694856)))) (.node (.leaf (.eqSym 6 16 1 13626888)) (.leaf (.eqSym 6 16 3 583426078))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 6 19 4 (-758940621))) (.leaf (.eqSym 6 19 5 (-1625744068)))) (.node (.leaf (.eqSym 6 19 6 1494624417)) (.leaf (.eqSym 6 20 6 (-5310752922)))))
            (.node (.node (.leaf (.eqSym 7 8 1 (-6147480504))) (.leaf (.eqSym 7 8 7 (-4661105332)))) (.node (.leaf (.eqSym 7 9 4 (-14763565131))) (.leaf (.eqSym 7 9 6 (-10369934239))))))
            (.node
            (.node (.node (.leaf (.eqSym 7 10 0 3486678395)) (.leaf (.eqSym 7 10 1 (-1054041938)))) (.node (.leaf (.eqSym 7 10 2 3547364291)) (.leaf (.eqSym 7 10 3 (-3066944755)))))
            (.node (.node (.leaf (.eqSym 7 10 4 11544240593)) (.leaf (.eqSym 7 10 6 16030731527))) (.node (.leaf (.eqSym 7 10 7 2547885396)) (.leaf (.eqSym 7 11 0 (-2701319752))))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 7 11 4 3130641374)) (.leaf (.eqSym 7 11 7 (-3003507290)))) (.node (.leaf (.eqSym 7 12 1 (-1444022221))) (.leaf (.eqSym 7 12 6 (-6644038274)))))
            (.node (.node (.leaf (.eqSym 7 13 1 2697020791)) (.leaf (.eqSym 7 13 3 3226378383))) (.node (.leaf (.eqSym 7 14 0 (-157549221))) (.leaf (.eqSym 7 14 3 (-4042834198))))))
            (.node
            (.node (.node (.leaf (.eqSym 7 14 7 625423093)) (.leaf (.eqSym 7 15 1 224804654))) (.node (.leaf (.eqSym 7 15 7 (-153660195))) (.leaf (.eqSym 7 16 3 (-1093828957)))))
            (.node (.node (.leaf (.eqSym 7 17 3 (-935044292))) (.leaf (.eqSym 7 17 4 4408654327))) (.node (.leaf (.eqSym 7 17 5 (-4228716503))) (.leaf (.eqSym 7 17 6 (-1295363150)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 7 17 7 (-1523611620))) (.leaf (.eqSym 7 18 5 (-537516117)))) (.node (.leaf (.eqSym 7 18 6 3483457397)) (.leaf (.eqSym 7 18 7 4201246829))))
            (.node (.node (.leaf (.eqSym 7 19 6 (-22398498))) (.leaf (.eqSym 7 19 7 (-2762649774)))) (.node (.leaf (.eqSym 8 9 3 (-18577622805))) (.leaf (.eqSym 8 9 5 2645972615)))))
            (.node
            (.node (.node (.leaf (.eqSym 8 10 0 (-4320692449))) (.leaf (.eqSym 8 10 2 12631611554))) (.node (.leaf (.eqSym 8 10 7 (-7360676148))) (.leaf (.eqSym 8 10 8 6992935308))))
            (.node (.node (.leaf (.eqSym 8 11 0 4603624601)) (.leaf (.eqSym 8 11 2 (-5078770183)))) (.node (.leaf (.eqSym 8 11 4 1721863404)) (.leaf (.eqSym 8 11 8 (-3033103985)))))))))))
      (.node
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 8 12 1 (-2391452833))) (.node (.leaf (.eqSym 8 12 6 4059949379)) (.leaf (.eqSym 8 13 1 (-1615413923)))))
            (.node (.node (.leaf (.eqSym 8 13 3 2027410773)) (.leaf (.eqSym 8 13 4 (-2909894308)))) (.node (.leaf (.eqSym 8 14 2 1065017210)) (.leaf (.eqSym 8 14 7 258160617)))))
            (.node
            (.node (.node (.leaf (.eqSym 8 16 4 1561700609)) (.leaf (.eqSym 8 16 5 (-334443448)))) (.node (.leaf (.eqSym 8 16 8 755455069)) (.leaf (.eqSym 8 19 6 (-1385346231)))))
            (.node (.node (.leaf (.eqSym 8 19 7 736760887)) (.leaf (.eqSym 8 19 8 (-2003680335)))) (.node (.leaf (.eqSym 8 20 7 344460356)) (.leaf (.eqSym 8 20 8 1083817384))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 9 10 0 558021031)) (.leaf (.eqSym 9 10 1 12327669353))) (.node (.leaf (.eqSym 9 10 3 (-3708548617))) (.leaf (.eqSym 9 10 6 (-5569828318)))))
            (.node (.node (.leaf (.eqSym 9 10 9 (-7472968479))) (.leaf (.eqSym 9 11 0 (-265597567)))) (.node (.leaf (.eqSym 9 11 1 (-9619675115))) (.leaf (.eqSym 9 11 5 (-3649166378))))))
            (.node
            (.node (.node (.leaf (.eqSym 9 11 8 (-4800604431))) (.leaf (.eqSym 9 11 9 5067488137))) (.node (.leaf (.eqSym 9 12 1 1097137624)) (.leaf (.eqSym 9 12 9 2190787990))))
            (.node (.node (.leaf (.eqSym 9 13 1 456289168)) (.leaf (.eqSym 9 13 4 (-2696179204)))) (.node (.leaf (.eqSym 9 14 7 (-2000967702))) (.leaf (.eqSym 9 15 5 283309280)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 9 16 8 14595716985)) (.node (.leaf (.eqSym 9 18 7 2347873838)) (.leaf (.eqSym 9 18 8 (-10441443809)))))
            (.node (.node (.leaf (.eqSym 9 18 9 (-11183315768))) (.leaf (.eqSym 9 19 7 2813893230))) (.node (.leaf (.eqSym 9 19 8 3544014282)) (.leaf (.eqSym 9 19 9 5791625481)))))
            (.node
            (.node (.node (.leaf (.eqSym 9 20 8 (-5677065668))) (.leaf (.eqSym 9 20 9 3687112563))) (.node (.leaf (.eqSym 10 11 0 131157861)) (.leaf (.eqSym 10 11 2 9768298983))))
            (.node (.node (.leaf (.eqSym 10 11 5 (-1679673640))) (.leaf (.eqSym 10 11 7 7379240663))) (.node (.leaf (.eqSym 10 11 9 1391748363)) (.leaf (.eqSym 10 11 10 1811667569))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 10 12 1 (-235390459))) (.leaf (.eqSym 10 12 3 3441253973))) (.node (.leaf (.eqSym 10 12 7 1596267348)) (.leaf (.eqSym 10 13 3 (-3486583044)))))
            (.node (.node (.leaf (.eqSym 10 13 8 1083004891)) (.leaf (.eqSym 10 13 9 (-3304517841)))) (.node (.leaf (.eqSym 10 14 7 (-5942048548))) (.leaf (.eqSym 10 15 7 6056127537)))))
            (.node
            (.node (.node (.leaf (.eqSym 10 15 8 1668241586)) (.leaf (.eqSym 10 16 6 (-270455156)))) (.node (.leaf (.eqSym 10 16 8 (-214031015))) (.leaf (.eqSym 10 16 9 (-15311706704)))))
            (.node (.node (.leaf (.eqSym 10 16 10 577352417)) (.leaf (.eqSym 10 17 8 4808765685))) (.node (.leaf (.eqSym 10 17 9 (-797861520))) (.leaf (.eqSym 10 17 10 2876309530))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 10 18 7 870316251)) (.node (.leaf (.eqSym 10 18 8 (-9322318095))) (.leaf (.eqSym 10 18 9 8455941060))))
            (.node (.node (.leaf (.eqSym 10 18 10 5915051771)) (.leaf (.eqSym 10 19 8 (-3300671691)))) (.node (.leaf (.eqSym 10 20 9 7289325119)) (.leaf (.eqSym 10 20 10 (-7427641610))))))
            (.node
            (.node (.node (.leaf (.eqSym 11 12 3 1757248453)) (.leaf (.eqSym 11 12 4 (-3927581605)))) (.node (.leaf (.eqSym 11 12 6 4280526074)) (.leaf (.eqSym 11 12 9 65971680))))
            (.node (.node (.leaf (.eqSym 11 12 11 (-2620120134))) (.leaf (.eqSym 11 13 4 2524037724))) (.node (.leaf (.eqSym 11 13 9 (-4082746650))) (.leaf (.eqSym 11 13 10 6861016391))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 11 14 4 275903426)) (.leaf (.eqSym 11 14 7 6552696904))) (.node (.leaf (.eqSym 11 14 9 2797219036)) (.leaf (.eqSym 11 14 11 (-713332949)))))
            (.node (.node (.leaf (.eqSym 11 15 5 (-1532344384))) (.leaf (.eqSym 11 15 8 (-10763992446)))) (.node (.leaf (.eqSym 11 15 11 (-303860151))) (.leaf (.eqSym 11 16 6 (-95258388))))))
            (.node
            (.node (.node (.leaf (.eqSym 11 16 8 (-1060858280))) (.leaf (.eqSym 11 16 10 1664437015))) (.node (.leaf (.eqSym 11 17 7 601099902)) (.leaf (.eqSym 11 17 8 (-3528267052)))))
            (.node (.node (.leaf (.eqSym 11 17 10 1774305639)) (.leaf (.eqSym 11 17 11 (-3585088378)))) (.node (.leaf (.eqSym 11 18 9 8371122370)) (.leaf (.eqSym 11 18 11 2676146433)))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 11 19 9 2013632136)) (.leaf (.eqSym 11 19 10 (-4981539370)))) (.node (.leaf (.eqSym 11 19 11 (-2180656423))) (.leaf (.eqSym 11 20 10 (-715944963)))))
            (.node (.node (.leaf (.eqSym 11 20 11 3258699345)) (.leaf (.eqSym 11 21 11 (-77317905)))) (.node (.leaf (.eqSym 12 13 4 833418756)) (.leaf (.eqSym 12 13 9 7044436653)))))
            (.node
            (.node (.node (.leaf (.eqSym 12 13 10 (-4678472215))) (.leaf (.eqSym 12 13 12 (-1188175530)))) (.node (.leaf (.eqSym 12 15 7 (-69868802))) (.leaf (.eqSym 12 16 8 882553778))))
            (.node (.node (.leaf (.eqSym 12 17 11 (-945056469))) (.leaf (.eqSym 12 18 9 (-969305062)))) (.node (.leaf (.eqSym 12 18 11 (-213123534))) (.leaf (.eqSym 12 19 11 276662080))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 12 20 11 324015535)) (.leaf (.eqSym 13 14 6 (-280116592)))) (.node (.leaf (.eqSym 13 14 7 (-1241405712))) (.leaf (.eqSym 13 15 7 2332233584))))
            (.node (.node (.leaf (.eqSym 13 15 10 3736312355)) (.leaf (.eqSym 13 16 8 (-723849689)))) (.node (.leaf (.eqSym 13 16 9 (-744669969))) (.leaf (.eqSym 13 16 13 259426822)))))
            (.node
            (.node (.node (.leaf (.eqSym 13 17 12 (-1201706365))) (.leaf (.eqSym 13 18 12 (-1655897596)))) (.node (.leaf (.eqSym 13 19 12 1292583696)) (.leaf (.eqSym 13 19 13 472828673))))
            (.node (.node (.leaf (.eqSym 13 20 12 (-379416993))) (.leaf (.eqSym 14 15 8 (-263589128)))) (.node (.leaf (.eqSym 14 15 11 1712694232)) (.leaf (.eqSym 14 15 13 (-991233437))))))))))
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 14 15 14 1384114988)) (.node (.leaf (.eqSym 14 17 14 1264363184)) (.leaf (.eqSym 14 18 14 (-692962246)))))
            (.node (.node (.leaf (.eqSym 14 20 13 (-393445746))) (.leaf (.eqSym 14 20 14 (-154798870)))) (.node (.leaf (.eqSym 14 21 14 366736851)) (.leaf (.eqSym 15 16 10 847823858)))))
            (.node
            (.node (.node (.leaf (.eqSym 15 16 12 1145301290)) (.leaf (.eqSym 15 16 13 570749374))) (.node (.leaf (.eqSym 15 16 14 896021694)) (.leaf (.eqSym 15 16 15 (-942447335)))))
            (.node (.node (.leaf (.eqSym 15 17 14 1185903810)) (.leaf (.eqSym 15 18 14 (-840428283)))) (.node (.leaf (.eqSym 15 18 15 (-834626279))) (.leaf (.eqSym 15 19 14 (-1659596120)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 15 20 14 399407414)) (.leaf (.eqSym 15 20 15 1511950027))) (.node (.leaf (.eqSym 15 21 15 (-486126545))) (.leaf (.eqSym 16 19 14 63021648))))
            (.node (.node (.leaf (.eqSym 16 19 15 1264270305)) (.leaf (.eqSym 16 19 16 333425640))) (.node (.leaf (.eqSym 16 20 15 (-2126774275))) (.leaf (.eqSym 16 20 16 (-1088939962))))))
            (.node
            (.node (.node (.leaf (.eqSym 17 18 15 (-1939199542))) (.leaf (.eqSym 17 18 16 2497427236))) (.node (.leaf (.eqSym 17 18 17 61153034)) (.leaf (.eqSym 17 19 15 93504429))))
            (.node (.node (.leaf (.eqSym 17 19 16 1093970004)) (.leaf (.eqSym 17 19 17 (-1524866413)))) (.node (.leaf (.eqSym 18 19 17 (-267437597))) (.leaf (.eqSym 18 19 18 1088759616)))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 18 20 17 (-841271427))) (.leaf (.eqSym 18 20 18 (-542344776)))) (.node (.leaf (.eqSym 18 21 18 638607860)) (.leaf (.eqSym 19 20 18 874671713))))
            (.node (.node (.leaf (.eqSym 19 20 19 368698249)) (.leaf (.eqSym 19 21 19 (-615606005)))) (.node (.leaf (.eqSym 20 21 20 792066261)) (.leaf (.ubHGe0 1 0 0 5499494176)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 1 0 1 10857975680)) (.leaf (.ubHLePi 1 1 0 2016481198))) (.node (.leaf (.ubHGe0 1 1 20 582104430)) (.leaf (.ubHMcc 2 0 17 89905179))))
            (.node (.node (.leaf (.ubHMcc 2 1 1 553679756)) (.leaf (.ubHMcc 2 1 19 2238966969))) (.node (.leaf (.ubHLePi 2 2 0 827132899)) (.leaf (.ubHMcc 2 2 2 4185493427))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 2 2 13 170465382)) (.leaf (.ubHLePi 2 2 19 238318625))) (.node (.leaf (.ubHLePi 3 0 16 49843368)) (.leaf (.ubHLePj 3 1 0 5779807823))))
            (.node (.node (.leaf (.ubHLePi 3 3 2 4268575273)) (.leaf (.ubHLePi 4 4 1 656995806))) (.node (.leaf (.ubHGe0 5 0 0 5313605722)) (.leaf (.ubHLePj 5 0 1 4133765196)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 5 0 5 184898766)) (.leaf (.ubHGe0 5 0 14 54627460))) (.node (.leaf (.ubHLePj 5 1 0 4867012290)) (.leaf (.ubHLePj 5 1 1 302546438))))
            (.node (.node (.leaf (.ubHLePj 5 1 16 51639757)) (.leaf (.ubHLePj 5 2 16 29421360))) (.node (.leaf (.ubHLePj 5 5 6 75951932)) (.leaf (.ubHLePj 6 0 2 533158758))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePj 6 5 15 1776465281)) (.node (.leaf (.ubHLePi 6 6 0 175804863)) (.leaf (.ubHLePj 6 6 14 4094417828))))
            (.node (.node (.leaf (.ubHGe0 6 6 15 55711996)) (.leaf (.ubHLePj 7 0 12 5696385))) (.node (.leaf (.ubHGe0 7 5 0 3495744016)) (.leaf (.ubHLePi 7 7 0 2185976329)))))
            (.node
            (.node (.node (.leaf (.ubHLePj 7 7 2 2375080455)) (.leaf (.ubHGe0 8 0 0 4159568411))) (.node (.leaf (.ubHLePj 8 0 1 5270476236)) (.leaf (.ubHLePj 8 1 0 7867046570))))
            (.node (.node (.leaf (.ubHLePi 9 8 0 25178532)) (.leaf (.ubHLePi 9 9 0 2514057878))) (.node (.leaf (.ubHGe0 10 0 0 1487837641)) (.leaf (.ubHLePj 10 0 1 12998431760))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 10 0 5 63534752)) (.leaf (.ubHLePj 10 0 11 1071047))) (.node (.leaf (.ubHMcc 10 10 2 1933570316)) (.leaf (.ubHMcc 11 1 1 117656948))))
            (.node (.node (.leaf (.ubHLePi 11 6 10 4101854)) (.leaf (.ubHMcc 11 10 9 48132823))) (.node (.leaf (.ubHMcc 11 10 10 1934145662)) (.leaf (.ubHLePi 11 11 0 3090676949)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 12 0 0 6338255845)) (.leaf (.ubHLePj 12 0 1 7439041919))) (.node (.leaf (.ubHLePj 12 1 0 10734592544)) (.leaf (.ubHMcc 12 2 9 63777126))))
            (.node (.node (.leaf (.ubHLePi 12 12 1 54402130)) (.leaf (.ubHLePi 12 12 2 1763650449))) (.node (.leaf (.ubHLePj 13 1 0 175980173)) (.leaf (.ubHGe0 14 0 0 230399813)))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePj 14 1 0 501277037)) (.leaf (.ubHLePj 14 2 7 128535636))) (.node (.leaf (.ubHGe0 14 14 2 1105668594)) (.leaf (.ubHLePi 15 15 0 1056257761))))
            (.node (.node (.leaf (.ubHGe0 16 2 5 119723474)) (.leaf (.ubHGe0 16 5 0 103021184))) (.node (.leaf (.ubHLePj 16 10 0 54478887)) (.leaf (.ubHGe0 16 11 5 248520)))))
            (.node
            (.node (.node (.leaf (.ubHLePj 16 15 5 2226067290)) (.leaf (.ubHLePj 16 16 2 356718359))) (.node (.leaf (.ubHGe0 17 0 0 364132468)) (.leaf (.ubHLePj 17 0 1 5121990875))))
            (.node (.node (.leaf (.ubHLePi 17 16 0 126961388)) (.leaf (.ubHLePi 17 17 0 215624026))) (.node (.leaf (.ubHGe0 18 0 0 843757847)) (.leaf (.ubHLePj 18 0 1 270822781))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePj 18 1 0 1270022286)) (.leaf (.ubHLePj 19 0 1 261792396))) (.node (.leaf (.ubHLePj 19 1 0 19682529400)) (.leaf (.ubHLePi 19 4 1 80641566))))
            (.node (.node (.leaf (.ubHMcc 19 7 2 2016906)) (.leaf (.ubHMcc 19 12 0 18561527))) (.node (.leaf (.ubHLePi 19 15 1 43132569)) (.leaf (.ubHMcc 19 18 1 38426568)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 19 19 0 115367588)) (.leaf (.ubHGe0 20 0 0 9052645924))) (.node (.leaf (.ubHLePj 20 0 1 361723225)) (.leaf (.ubHMcc 20 2 0 19134105499))))
            (.node (.node (.leaf (.ubHMcc 20 11 0 1459470322)) (.leaf (.ubHLePi 20 16 0 396768952))) (.node (.leaf (.ubHMcc 20 18 1 1845086146)) (.leaf (.ubHLePj 21 1 0 8531205015)))))))))))
    (.node
      (.node
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePj 21 11 0 5649477)) (.node (.leaf (.ubHLePj 21 20 0 669217707)) (.leaf (.ubHGe0 0 0 6 4690))))
            (.node (.node (.leaf (.ubHLePi 0 0 5 25961)) (.leaf (.ubHGe0 0 0 4 60186))) (.node (.leaf (.ubHLePi 0 0 3 74768)) (.leaf (.ubHGe0 0 0 2 52470)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 0 0 1 19714)) (.leaf (.ubHGe0 0 0 0 3097))) (.node (.leaf (.ubHLePi 1 0 6 17686)) (.leaf (.ubHLePi 1 1 5 7986))))
            (.node (.node (.leaf (.ubHGe0 1 0 5 106616)) (.leaf (.ubHGe0 1 1 4 37168))) (.node (.leaf (.ubHLePi 1 0 4 267489)) (.leaf (.ubHLePi 1 1 3 69540))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 1 0 3 357635)) (.leaf (.ubHGe0 1 1 2 65334))) (.node (.leaf (.ubHLePi 1 0 2 268810)) (.leaf (.ubHLePi 1 1 1 30807))))
            (.node (.node (.leaf (.ubHGe0 1 0 1 107712)) (.leaf (.ubHGe0 1 1 0 5830))) (.node (.leaf (.ubHLePi 1 0 0 17978)) (.leaf (.ubHGe0 2 0 6 20890)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 2 1 5 5549)) (.leaf (.ubHLePi 2 2 4 216))) (.node (.leaf (.ubHLePi 2 0 5 120333)) (.leaf (.ubHLePi 2 1 4 25021))))
            (.node (.node (.leaf (.ubHGe0 2 2 3 823)) (.leaf (.ubHGe0 2 0 4 290016))) (.node (.leaf (.ubHGe0 2 1 3 45385)) (.leaf (.ubHLePi 2 2 2 1177)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 2 0 3 374004)) (.node (.leaf (.ubHLePi 2 1 2 41355)) (.leaf (.ubHGe0 2 2 1 751))))
            (.node (.node (.leaf (.ubHGe0 2 0 2 272017)) (.leaf (.ubHGe0 2 1 1 18915))) (.node (.leaf (.ubHLePi 2 0 1 105742)) (.leaf (.ubHLePi 2 1 0 3471)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 2 0 0 17158)) (.leaf (.ubHLePi 3 0 6 13825))) (.node (.leaf (.ubHLePi 3 1 5 14464)) (.leaf (.ubHLePi 3 2 4 3158))))
            (.node (.node (.leaf (.ubHLePi 3 3 3 354)) (.leaf (.ubHGe0 3 0 5 90795))) (.node (.leaf (.ubHGe0 3 1 4 73342)) (.leaf (.ubHGe0 3 2 3 12832))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 3 3 2 991)) (.leaf (.ubHLePi 3 0 4 246942))) (.node (.leaf (.ubHLePi 3 1 3 149528)) (.leaf (.ubHLePi 3 2 2 19509))))
            (.node (.node (.leaf (.ubHLePi 3 3 1 930)) (.leaf (.ubHGe0 3 0 3 356551))) (.node (.leaf (.ubHGe0 3 1 2 153009)) (.leaf (.ubHGe0 3 2 1 13158)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 3 3 0 292)) (.leaf (.ubHLePi 3 0 2 288545))) (.node (.leaf (.ubHLePi 3 1 1 78504)) (.leaf (.ubHLePi 3 2 0 3323))))
            (.node (.node (.leaf (.ubHGe0 3 0 1 124179)) (.leaf (.ubHGe0 3 1 0 16144))) (.node (.leaf (.ubHLePi 3 0 0 22214)) (.leaf (.ubHLePi 4 0 6 17305))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 4 1 5 14412)) (.node (.leaf (.ubHLePi 4 2 4 5474)) (.leaf (.ubHLePi 4 3 3 916))))
            (.node (.node (.leaf (.ubHLePi 4 4 2 55)) (.leaf (.ubHGe0 4 0 5 109067))) (.node (.leaf (.ubHGe0 4 1 4 76981)) (.leaf (.ubHGe0 4 2 3 22900)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 4 3 2 2748)) (.leaf (.ubHGe0 4 4 1 100))) (.node (.leaf (.ubHLePi 4 0 4 288953)) (.leaf (.ubHLePi 4 1 3 164940))))
            (.node (.node (.leaf (.ubHLePi 4 2 2 35936)) (.leaf (.ubHLePi 4 3 1 2748))) (.node (.leaf (.ubHLePi 4 4 0 46)) (.leaf (.ubHGe0 4 0 3 411149))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 4 1 2 177012)) (.leaf (.ubHGe0 4 2 1 25057))) (.node (.leaf (.ubHGe0 4 3 0 916)) (.leaf (.ubHLePi 4 0 2 330894))))
            (.node (.node (.leaf (.ubHLePi 4 1 1 95072)) (.leaf (.ubHLePi 4 2 0 6548))) (.node (.leaf (.ubHGe0 4 0 1 142638)) (.leaf (.ubHGe0 4 1 0 20431)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 4 0 0 25703)) (.leaf (.ubHLePi 5 0 6 10042))) (.node (.leaf (.ubHLePi 5 1 5 15540)) (.leaf (.ubHLePi 5 2 4 6755))))
            (.node (.node (.leaf (.ubHLePi 5 3 3 859)) (.leaf (.ubHLePi 5 4 2 5))) (.node (.leaf (.ubHGe0 5 5 1 1)) (.leaf (.ubHGe0 5 1 4 84938)))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 5 2 3 27769)) (.leaf (.ubHGe0 5 3 2 2486))) (.node (.leaf (.ubHGe0 5 4 1 7)) (.leaf (.ubHLePi 5 5 0 1))))
            (.node (.node (.leaf (.ubHLePi 5 0 4 203966)) (.leaf (.ubHLePi 5 1 3 185022))) (.node (.leaf (.ubHLePi 5 2 2 42756)) (.leaf (.ubHLePi 5 3 1 2397)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 5 4 0 2)) (.leaf (.ubHGe0 5 0 3 312952))) (.node (.leaf (.ubHGe0 5 1 2 200801)) (.leaf (.ubHGe0 5 2 1 29223))))
            (.node (.node (.leaf (.ubHGe0 5 3 0 770)) (.leaf (.ubHLePi 5 0 2 268362))) (.node (.leaf (.ubHLePi 5 1 1 108588)) (.leaf (.ubHLePi 5 2 0 7481))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 5 0 1 122009)) (.leaf (.ubHGe0 5 1 0 23411))) (.node (.leaf (.ubHLePi 5 0 0 22987)) (.leaf (.ubHGe0 6 0 6 717))))
            (.node (.node (.leaf (.ubHGe0 6 1 5 4127)) (.leaf (.ubHGe0 6 2 4 4150))) (.node (.leaf (.ubHGe0 6 3 3 2087)) (.leaf (.ubHGe0 6 4 2 486)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 6 5 1 42)) (.leaf (.ubHGe0 6 6 0 1))) (.node (.leaf (.ubHLePi 6 0 5 8018)) (.leaf (.ubHLePi 6 1 4 26436))))
            (.node (.node (.leaf (.ubHLePi 6 2 3 20883)) (.leaf (.ubHLePi 6 3 2 7482))) (.node (.leaf (.ubHLePi 6 4 1 1068)) (.leaf (.ubHLePi 6 5 0 41)))))))))
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHGe0 6 0 4 31155)) (.node (.leaf (.ubHGe0 6 1 3 67906)) (.leaf (.ubHGe0 6 2 2 39186))))
            (.node (.node (.leaf (.ubHGe0 6 3 1 8842)) (.leaf (.ubHGe0 6 4 0 582))) (.node (.leaf (.ubHLePi 6 0 3 59959)) (.leaf (.ubHLePi 6 1 2 87145)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 6 2 1 32416)) (.leaf (.ubHLePi 6 3 0 3446))) (.node (.leaf (.ubHGe0 6 0 2 62464)) (.leaf (.ubHGe0 6 1 1 55715))))
            (.node (.node (.leaf (.ubHGe0 6 2 0 9963)) (.leaf (.ubHLePi 6 0 1 33902))) (.node (.leaf (.ubHLePi 6 1 0 14167)) (.leaf (.ubHGe0 6 0 0 7542))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 7 0 6 1946)) (.leaf (.ubHLePi 7 1 5 3778))) (.node (.leaf (.ubHLePi 7 2 4 6781)) (.leaf (.ubHLePi 7 3 3 4017))))
            (.node (.node (.leaf (.ubHLePi 7 4 2 785)) (.leaf (.ubHLePi 7 5 1 19))) (.node (.leaf (.ubHGe0 7 0 5 14052)) (.leaf (.ubHGe0 7 1 4 30124)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 7 2 3 36309)) (.leaf (.ubHGe0 7 3 2 14108))) (.node (.leaf (.ubHGe0 7 4 1 1577)) (.leaf (.ubHLePi 7 0 4 46298))))
            (.node (.node (.leaf (.ubHLePi 7 1 3 90083)) (.leaf (.ubHLePi 7 2 2 70516))) (.node (.leaf (.ubHLePi 7 3 1 16147)) (.leaf (.ubHLePi 7 4 0 788)))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 7 0 3 85464)) (.leaf (.ubHGe0 7 1 2 128476))) (.node (.leaf (.ubHGe0 7 2 1 59200)) (.leaf (.ubHGe0 7 3 0 6052))))
            (.node (.node (.leaf (.ubHLePi 7 0 2 90224)) (.leaf (.ubHLePi 7 1 1 88297))) (.node (.leaf (.ubHLePi 7 2 0 18210)) (.leaf (.ubHGe0 7 0 1 50655)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 7 1 0 23557)) (.leaf (.ubHLePi 7 0 0 11703))) (.node (.leaf (.ubHGe0 8 0 6 1343)) (.leaf (.ubHGe0 8 1 5 3837))))
            (.node (.node (.leaf (.ubHGe0 8 2 4 3989)) (.leaf (.ubHGe0 8 3 3 1231))) (.node (.leaf (.ubHLePi 8 4 2 70)) (.leaf (.ubHLePi 8 5 1 8))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 8 0 5 10804)) (.leaf (.ubHLePi 8 1 4 25093))) (.node (.leaf (.ubHLePi 8 2 3 18134)) (.leaf (.ubHLePi 8 3 2 3004))))
            (.node (.node (.leaf (.ubHGe0 8 4 1 270)) (.leaf (.ubHGe0 8 5 0 16))) (.node (.leaf (.ubHGe0 8 0 4 36456)) (.leaf (.ubHGe0 8 1 3 63475)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 8 2 2 29271)) (.leaf (.ubHGe0 8 3 1 2036))) (.node (.leaf (.ubHLePi 8 4 0 218)) (.leaf (.ubHLePi 8 0 3 64877))))
            (.node (.node (.leaf (.ubHLePi 8 1 2 77400)) (.leaf (.ubHLePi 8 2 1 19836))) (.node (.leaf (.ubHLePi 8 3 0 243)) (.leaf (.ubHGe0 8 0 2 63622))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHGe0 8 1 1 45450)) (.node (.leaf (.ubHGe0 8 2 0 4697)) (.leaf (.ubHLePi 8 0 1 32448))))
            (.node (.node (.leaf (.ubHLePi 8 1 0 10264)) (.leaf (.ubHLePi 9 0 6 590))) (.node (.leaf (.ubHLePi 9 1 5 4527)) (.leaf (.ubHLePi 9 2 4 10152)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 9 3 3 9636)) (.leaf (.ubHLePi 9 4 2 3692))) (.node (.leaf (.ubHLePi 9 5 1 479)) (.leaf (.ubHGe0 9 6 0 28))))
            (.node (.node (.leaf (.ubHGe0 9 0 5 7510)) (.leaf (.ubHGe0 9 1 4 39846))) (.node (.leaf (.ubHGe0 9 2 3 64641)) (.leaf (.ubHGe0 9 3 2 40584))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 9 4 1 9102)) (.leaf (.ubHGe0 9 5 0 335))) (.node (.leaf (.ubHLePi 9 0 4 36141)) (.leaf (.ubHLePi 9 1 3 134777))))
            (.node (.node (.leaf (.ubHLePi 9 2 2 147480)) (.leaf (.ubHLePi 9 3 1 54937))) (.node (.leaf (.ubHLePi 9 4 0 5109)) (.leaf (.ubHGe0 9 0 3 87343)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 9 1 2 218700)) (.leaf (.ubHGe0 9 2 1 143837))) (.node (.leaf (.ubHGe0 9 3 0 23646)) (.leaf (.ubHLePi 9 0 2 113187))))
            (.node (.node (.leaf (.ubHLePi 9 1 1 170756)) (.leaf (.ubHLePi 9 2 0 50622))) (.node (.leaf (.ubHGe0 9 0 1 75068)) (.leaf (.ubHGe0 9 1 0 51434)))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 9 0 0 19990)) (.leaf (.ubHLePi 10 0 6 241))) (.node (.leaf (.ubHLePi 10 1 5 1256)) (.leaf (.ubHLePi 10 2 4 2301))))
            (.node (.node (.leaf (.ubHLePi 10 3 3 1551)) (.leaf (.ubHGe0 10 4 2 134))) (.node (.leaf (.ubHGe0 10 5 1 381)) (.leaf (.ubHGe0 10 6 0 14)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 10 0 5 2456)) (.leaf (.ubHGe0 10 1 4 10098))) (.node (.leaf (.ubHGe0 10 2 3 13052)) (.leaf (.ubHGe0 10 3 2 4073))))
            (.node (.node (.leaf (.ubHLePi 10 4 1 1874)) (.leaf (.ubHLePi 10 5 0 455))) (.node (.leaf (.ubHLePi 10 0 4 10362)) (.leaf (.ubHLePi 10 1 3 31174))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 10 2 2 24471)) (.leaf (.ubHLePi 10 3 1 701))) (.node (.leaf (.ubHGe0 10 4 0 1907)) (.leaf (.ubHGe0 10 0 3 22664))))
            (.node (.node (.leaf (.ubHGe0 10 1 2 44903)) (.leaf (.ubHGe0 10 2 1 16514))) (.node (.leaf (.ubHLePi 10 3 0 2021)) (.leaf (.ubHLePi 10 0 2 26632)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 10 1 1 29283)) (.leaf (.ubHLePi 10 2 0 2658))) (.node (.leaf (.ubHGe0 10 0 1 15680)) (.leaf (.ubHGe0 10 1 0 6663))))
            (.node (.node (.leaf (.ubHLePi 10 0 0 3558)) (.leaf (.ubHLePi 11 0 6 362))) (.node (.leaf (.ubHLePi 11 1 5 2315)) (.leaf (.ubHLePi 11 2 4 5996))))))))))
      (.node
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 11 3 3 8175)) (.node (.leaf (.ubHLePi 11 4 2 6487)) (.leaf (.ubHLePi 11 5 1 2837))))
            (.node (.node (.leaf (.ubHLePi 11 6 0 743)) (.leaf (.ubHGe0 11 0 5 4055))) (.node (.leaf (.ubHGe0 11 1 4 21623)) (.leaf (.ubHGe0 11 2 3 44827)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 11 3 2 46769)) (.leaf (.ubHGe0 11 4 1 24967))) (.node (.leaf (.ubHGe0 11 5 0 6493)) (.leaf (.ubHLePi 11 0 4 19247))))
            (.node (.node (.leaf (.ubHLePi 11 1 3 81616)) (.leaf (.ubHLePi 11 2 2 127858))) (.node (.leaf (.ubHLePi 11 3 1 89828)) (.leaf (.ubHLePi 11 4 0 26243))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 11 0 3 49095)) (.leaf (.ubHGe0 11 1 2 155758))) (.node (.leaf (.ubHGe0 11 2 1 163607)) (.leaf (.ubHGe0 11 3 0 60235))))
            (.node (.node (.leaf (.ubHLePi 11 0 2 70890)) (.leaf (.ubHLePi 11 1 1 149817))) (.node (.leaf (.ubHLePi 11 2 0 80554)) (.leaf (.ubHGe0 11 0 1 54869)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 11 1 0 58512)) (.leaf (.ubHLePi 11 0 0 17844))) (.node (.leaf (.ubHGe0 12 0 6 54)) (.leaf (.ubHGe0 12 1 5 288))))
            (.node (.node (.leaf (.ubHGe0 12 2 4 756)) (.leaf (.ubHGe0 12 3 3 1057))) (.node (.leaf (.ubHGe0 12 4 2 907)) (.leaf (.ubHGe0 12 5 1 266)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 12 6 0 311)) (.node (.leaf (.ubHLePi 12 0 5 535)) (.leaf (.ubHLePi 12 1 4 2670))))
            (.node (.node (.leaf (.ubHLePi 12 2 3 5601)) (.leaf (.ubHLePi 12 3 2 6124))) (.node (.leaf (.ubHLePi 12 4 1 2841)) (.leaf (.ubHGe0 12 5 0 1406)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 12 0 4 2411)) (.leaf (.ubHGe0 12 1 3 9967))) (.node (.leaf (.ubHGe0 12 2 2 15975)) (.leaf (.ubHGe0 12 3 1 10721))))
            (.node (.node (.leaf (.ubHLePi 12 4 0 1834)) (.leaf (.ubHLePi 12 0 3 5977))) (.node (.leaf (.ubHLePi 12 1 2 18877)) (.leaf (.ubHLePi 12 2 1 19532))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 12 3 0 1093)) (.leaf (.ubHGe0 12 0 2 8475))) (.node (.leaf (.ubHGe0 12 1 1 17670)) (.leaf (.ubHGe0 12 2 0 5273))))
            (.node (.node (.leaf (.ubHLePi 12 0 1 6409)) (.leaf (.ubHLePi 12 1 0 5226))) (.node (.leaf (.ubHGe0 13 0 6 2)) (.leaf (.ubHLePi 13 1 5 56)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 13 2 4 641)) (.leaf (.ubHLePi 13 3 3 1662))) (.node (.leaf (.ubHLePi 13 4 2 808)) (.leaf (.ubHGe0 13 5 1 1002))))
            (.node (.node (.leaf (.ubHGe0 13 6 0 814)) (.leaf (.ubHGe0 13 0 5 46))) (.node (.leaf (.ubHGe0 13 1 4 1498)) (.leaf (.ubHGe0 13 2 3 7102))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHGe0 13 3 2 7740)) (.node (.leaf (.ubHLePi 13 4 1 2993)) (.leaf (.ubHLePi 13 5 0 5319))))
            (.node (.node (.leaf (.ubHLePi 13 0 4 839)) (.leaf (.ubHLePi 13 1 3 9576))) (.node (.leaf (.ubHLePi 13 2 2 21033)) (.leaf (.ubHLePi 13 3 1 1983)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 13 4 0 13465)) (.leaf (.ubHGe0 13 0 3 4118))) (.node (.leaf (.ubHGe0 13 1 2 22393)) (.leaf (.ubHGe0 13 2 1 15434))))
            (.node (.node (.leaf (.ubHLePi 13 3 0 15759)) (.leaf (.ubHLePi 13 0 2 8280))) (.node (.leaf (.ubHLePi 13 1 1 18096)) (.leaf (.ubHGe0 13 2 0 7127))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 13 0 1 6632)) (.leaf (.ubHGe0 13 1 0 897))) (.node (.leaf (.ubHLePi 13 0 0 1225)) (.leaf (.ubHGe0 14 0 6 1))))
            (.node (.node (.leaf (.ubHLePi 14 1 5 144)) (.leaf (.ubHLePi 14 2 4 1559))) (.node (.leaf (.ubHLePi 14 3 3 5915)) (.leaf (.ubHLePi 14 4 2 9074)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 14 5 1 5163)) (.leaf (.ubHLePi 14 6 0 1910))) (.node (.leaf (.ubHGe0 14 0 5 144)) (.leaf (.ubHGe0 14 1 4 3616))))
            (.node (.node (.leaf (.ubHGe0 14 2 3 22451)) (.leaf (.ubHGe0 14 3 2 50496))) (.node (.leaf (.ubHGe0 14 4 1 41099)) (.leaf (.ubHGe0 14 5 0 15264)))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 14 0 4 2058)) (.leaf (.ubHLePi 14 1 3 27926))) (.node (.leaf (.ubHLePi 14 2 2 102744)) (.leaf (.ubHLePi 14 3 1 124593))))
            (.node (.node (.leaf (.ubHLePi 14 4 0 54624)) (.leaf (.ubHGe0 14 0 3 11390))) (.node (.leaf (.ubHGe0 14 1 2 90921)) (.leaf (.ubHGe0 14 2 1 182008)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 14 3 0 107292)) (.leaf (.ubHLePi 14 0 2 29599))) (.node (.leaf (.ubHLePi 14 1 1 129081)) (.leaf (.ubHLePi 14 2 0 118850))))
            (.node (.node (.leaf (.ubHGe0 14 0 1 35729)) (.leaf (.ubHGe0 14 1 0 69499))) (.node (.leaf (.ubHLePi 14 0 0 16671)) (.leaf (.ubHGe0 15 0 6 1))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 15 1 5 48)) (.leaf (.ubHGe0 15 2 4 657))) (.node (.leaf (.ubHGe0 15 3 3 3698)) (.leaf (.ubHGe0 15 4 2 9661))))
            (.node (.node (.leaf (.ubHGe0 15 5 1 12019)) (.leaf (.ubHGe0 15 6 0 5366))) (.node (.leaf (.ubHLePi 15 0 5 48)) (.leaf (.ubHLePi 15 1 4 1446)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 15 2 3 12875)) (.leaf (.ubHLePi 15 3 2 46477))) (.node (.leaf (.ubHLePi 15 4 1 73642)) (.leaf (.ubHLePi 15 5 0 40675))))
            (.node (.node (.leaf (.ubHGe0 15 0 4 789)) (.leaf (.ubHGe0 15 1 3 14844))) (.node (.leaf (.ubHGe0 15 2 2 83636)) (.leaf (.ubHGe0 15 3 1 180976)))))))))
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHGe0 15 4 0 128538)) (.node (.leaf (.ubHLePi 15 0 3 5666)) (.leaf (.ubHLePi 15 1 2 66610))))
            (.node (.node (.leaf (.ubHLePi 15 2 1 222396)) (.leaf (.ubHLePi 15 3 0 216537))) (.node (.leaf (.ubHGe0 15 0 2 19790)) (.leaf (.ubHGe0 15 1 1 136391)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 15 2 0 204892)) (.leaf (.ubHLePi 15 0 1 33348))) (.node (.leaf (.ubHLePi 15 1 0 103153)) (.leaf (.ubHGe0 15 0 0 21569))))
            (.node (.node (.leaf (.ubHGe0 16 1 5 1)) (.leaf (.ubHGe0 16 2 4 97))) (.node (.leaf (.ubHGe0 16 3 3 1588)) (.leaf (.ubHGe0 16 4 2 8320))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 16 5 1 14937)) (.leaf (.ubHGe0 16 6 0 6591))) (.node (.leaf (.ubHLePi 16 0 5 1)) (.leaf (.ubHLePi 16 1 4 180))))
            (.node (.node (.leaf (.ubHLePi 16 2 3 4728)) (.leaf (.ubHLePi 16 3 2 35128))) (.node (.leaf (.ubHLePi 16 4 1 84662)) (.leaf (.ubHLePi 16 5 0 51087)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 16 0 4 84)) (.leaf (.ubHGe0 16 1 3 4698))) (.node (.leaf (.ubHGe0 16 2 2 55502)) (.leaf (.ubHGe0 16 3 1 190461))))
            (.node (.node (.leaf (.ubHGe0 16 4 0 159568)) (.leaf (.ubHLePi 16 0 3 1558))) (.node (.leaf (.ubHLePi 16 1 2 38898)) (.leaf (.ubHLePi 16 2 1 212811)))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 16 3 0 259751)) (.leaf (.ubHGe0 16 0 2 10204))) (.node (.leaf (.ubHGe0 16 1 1 118199)) (.leaf (.ubHGe0 16 2 0 233788))))
            (.node (.node (.leaf (.ubHLePi 16 0 1 26125)) (.leaf (.ubHLePi 16 1 0 110719))) (.node (.leaf (.ubHGe0 16 0 0 21609)) (.leaf (.ubHLePi 17 2 4 21)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 17 3 3 98)) (.leaf (.ubHGe0 17 4 2 524))) (.node (.leaf (.ubHGe0 17 5 1 1270)) (.leaf (.ubHGe0 17 6 0 2965))))
            (.node (.node (.leaf (.ubHGe0 17 1 4 39)) (.leaf (.ubHGe0 17 2 3 358))) (.node (.leaf (.ubHLePi 17 3 2 1608)) (.leaf (.ubHLePi 17 4 1 6624))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 17 5 0 17112)) (.leaf (.ubHLePi 17 0 4 18))) (.node (.leaf (.ubHLePi 17 1 3 414)) (.leaf (.ubHGe0 17 2 2 1660))))
            (.node (.node (.leaf (.ubHGe0 17 3 1 13429)) (.leaf (.ubHGe0 17 4 0 41769))) (.node (.leaf (.ubHGe0 17 0 3 155)) (.leaf (.ubHLePi 17 1 2 594)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 17 2 1 13229)) (.leaf (.ubHLePi 17 3 0 54959))) (.node (.leaf (.ubHGe0 17 0 2 18)) (.leaf (.ubHGe0 17 1 1 6321))))
            (.node (.node (.leaf (.ubHGe0 17 2 0 40944)) (.leaf (.ubHLePi 17 0 1 1166))) (.node (.leaf (.ubHLePi 17 1 0 16314)) (.leaf (.ubHLePi 18 3 3 177))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 18 4 2 3204)) (.node (.leaf (.ubHLePi 18 5 1 10375)) (.leaf (.ubHLePi 18 6 0 17283))))
            (.node (.node (.leaf (.ubHGe0 18 2 3 485)) (.leaf (.ubHGe0 18 3 2 12330))) (.node (.leaf (.ubHGe0 18 4 1 53852)) (.leaf (.ubHGe0 18 5 0 105037)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 18 1 3 447)) (.leaf (.ubHLePi 18 2 2 17864))) (.node (.leaf (.ubHLePi 18 3 1 111596)) (.leaf (.ubHLePi 18 4 0 268419))))
            (.node (.node (.leaf (.ubHGe0 18 0 3 138)) (.leaf (.ubHGe0 18 1 2 11543))) (.node (.leaf (.ubHGe0 18 2 1 115424)) (.leaf (.ubHGe0 18 3 0 368411))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 18 0 2 2805)) (.leaf (.ubHLePi 18 1 1 59595))) (.node (.leaf (.ubHLePi 18 2 0 285956)) (.leaf (.ubHGe0 18 0 1 12290))))
            (.node (.node (.leaf (.ubHGe0 18 1 0 118853)) (.leaf (.ubHLePi 18 0 0 20644))) (.node (.leaf (.ubHLePi 19 4 2 273)) (.leaf (.ubHGe0 19 5 1 931)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 19 6 0 9802)) (.leaf (.ubHGe0 19 3 2 1024))) (.node (.leaf (.ubHGe0 19 5 0 53192)) (.leaf (.ubHLePi 19 2 2 1444))))
            (.node (.node (.leaf (.ubHGe0 19 3 1 6870)) (.leaf (.ubHLePi 19 4 0 121020))) (.node (.leaf (.ubHGe0 19 1 2 909)) (.leaf (.ubHLePi 19 2 1 5792)))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 19 3 0 147710)) (.leaf (.ubHLePi 19 0 2 215))) (.node (.leaf (.ubHGe0 19 1 1 2399)) (.leaf (.ubHLePi 19 2 0 101973))))
            (.node (.node (.leaf (.ubHLePi 19 0 1 388)) (.leaf (.ubHGe0 19 1 0 37743))) (.node (.leaf (.ubHLePi 19 0 0 5851)) (.leaf (.ubHGe0 20 5 1 1907)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 20 6 0 23600)) (.leaf (.ubHLePi 20 4 1 8398))) (.node (.leaf (.ubHGe0 20 5 0 131255)) (.leaf (.ubHGe0 20 3 1 14960))))
            (.node (.node (.leaf (.ubHLePi 20 4 0 305601)) (.leaf (.ubHLePi 20 2 1 13449))) (.node (.leaf (.ubHGe0 20 3 0 381067)) (.leaf (.ubHGe0 20 1 1 6093))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 20 2 0 268269)) (.leaf (.ubHLePi 20 0 1 1112))) (.node (.leaf (.ubHGe0 20 1 0 101056)) (.leaf (.ubHLePi 20 0 0 15908))))
            (.node (.node (.leaf (.ubHGe0 21 6 0 25316)) (.leaf (.ubHLePi 21 5 0 142380))) (.node (.leaf (.ubHGe0 21 4 0 335019)) (.leaf (.ubHLePi 21 3 0 421922)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 21 2 0 299833)) (.leaf (.ubHLePi 21 1 0 113956))) (.node (.leaf (.ubHGe0 21 0 0 18092)) (.leaf (.ubPHi 6 332341))))
            (.node (.node (.leaf (.ubPHi 5 668057)) (.leaf (.ubPHi 4 4304405))) (.node (.leaf (.ubPHi 3 1883345)) (.leaf (.ubPHi 2 3792896))))))))))))

lemma step1aScale_pos : 0 < step1aScale := by decide
lemma step1aLb_strict : 209 * (step1aScale : ℤ) < 210 * step1aLb := by decide
lemma step1aCert_u_ok :
    checkBinoBoundU 21 6 [] step1aCert 2 1 step1aScale step1aLb = true := by
  decide
private lemma step1aCert_c_0 : checkBinoCForJ 21 6 0 step1aCert = true := by decide
private lemma step1aCert_c_1 : checkBinoCForJ 21 6 1 step1aCert = true := by decide
private lemma step1aCert_c_2 : checkBinoCForJ 21 6 2 step1aCert = true := by decide
private lemma step1aCert_c_3 : checkBinoCForJ 21 6 3 step1aCert = true := by decide
private lemma step1aCert_c_4 : checkBinoCForJ 21 6 4 step1aCert = true := by decide
private lemma step1aCert_c_5 : checkBinoCForJ 21 6 5 step1aCert = true := by decide
private lemma step1aCert_c_6 : checkBinoCForJ 21 6 6 step1aCert = true := by decide
private lemma step1aCert_c_7 : checkBinoCForJ 21 6 7 step1aCert = true := by decide
private lemma step1aCert_c_8 : checkBinoCForJ 21 6 8 step1aCert = true := by decide
private lemma step1aCert_c_9 : checkBinoCForJ 21 6 9 step1aCert = true := by decide
private lemma step1aCert_c_10 : checkBinoCForJ 21 6 10 step1aCert = true := by decide
private lemma step1aCert_c_11 : checkBinoCForJ 21 6 11 step1aCert = true := by decide
private lemma step1aCert_c_12 : checkBinoCForJ 21 6 12 step1aCert = true := by decide
private lemma step1aCert_c_13 : checkBinoCForJ 21 6 13 step1aCert = true := by decide
private lemma step1aCert_c_14 : checkBinoCForJ 21 6 14 step1aCert = true := by decide
private lemma step1aCert_c_15 : checkBinoCForJ 21 6 15 step1aCert = true := by decide
private lemma step1aCert_c_16 : checkBinoCForJ 21 6 16 step1aCert = true := by decide
private lemma step1aCert_c_17 : checkBinoCForJ 21 6 17 step1aCert = true := by decide
private lemma step1aCert_c_18 : checkBinoCForJ 21 6 18 step1aCert = true := by decide
private lemma step1aCert_c_19 : checkBinoCForJ 21 6 19 step1aCert = true := by decide
private lemma step1aCert_c_20 : checkBinoCForJ 21 6 20 step1aCert = true := by decide
private lemma step1aCert_c_21 : checkBinoCForJ 21 6 21 step1aCert = true := by decide
lemma step1aCert_c_ok : ∀ j ≤ 21, checkBinoCForJ 21 6 j step1aCert = true := by
  intro j hj
  match j with
  | 0 => exact step1aCert_c_0
  | 1 => exact step1aCert_c_1
  | 2 => exact step1aCert_c_2
  | 3 => exact step1aCert_c_3
  | 4 => exact step1aCert_c_4
  | 5 => exact step1aCert_c_5
  | 6 => exact step1aCert_c_6
  | 7 => exact step1aCert_c_7
  | 8 => exact step1aCert_c_8
  | 9 => exact step1aCert_c_9
  | 10 => exact step1aCert_c_10
  | 11 => exact step1aCert_c_11
  | 12 => exact step1aCert_c_12
  | 13 => exact step1aCert_c_13
  | 14 => exact step1aCert_c_14
  | 15 => exact step1aCert_c_15
  | 16 => exact step1aCert_c_16
  | 17 => exact step1aCert_c_17
  | 18 => exact step1aCert_c_18
  | 19 => exact step1aCert_c_19
  | 20 => exact step1aCert_c_20
  | 21 => exact step1aCert_c_21
  | _ + 22 => omega

def step1bScale : ℕ := 1000000000
def step1bLb : ℤ := 959272736
def step1bCert : BinTree BinoStep :=
  (.node
    (.node
      (.node
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.eqP0 (-38840806043))) (.node (.leaf (.eqP1 135692950395)) (.leaf (.eqB00 0 (-439972675)))))
            (.node (.node (.leaf (.eqB01 0 1102079993)) (.leaf (.eqDiag 1 239135137))) (.node (.leaf (.eqB00 1 (-652186737))) (.leaf (.eqB01 1 1287650737)))))
            (.node
            (.node (.node (.leaf (.eqDiag 3 2223900001)) (.leaf (.eqDiag 4 325437056))) (.node (.leaf (.eqB10 5 2271685705)) (.leaf (.eqB00 6 (-1910918151)))))
            (.node (.node (.leaf (.eqB10 6 5359655800)) (.leaf (.eqDiag 7 1180437318))) (.node (.leaf (.eqDiag 8 2306639521)) (.leaf (.eqB01 8 3929715855))))))
            (.node
            (.node
            (.node (.leaf (.eqB00 9 (-11494456002))) (.node (.leaf (.eqB10 9 11511881438)) (.leaf (.eqB01 9 14721096653))))
            (.node (.node (.leaf (.eqDiag 10 1169353712)) (.leaf (.eqB10 10 4565705684))) (.node (.leaf (.eqDiag 11 311755477)) (.leaf (.eqB01 11 9195428328)))))
            (.node
            (.node (.node (.leaf (.eqDiag 12 694908560)) (.leaf (.eqB00 13 (-4302174943)))) (.node (.leaf (.eqB10 13 10741347812)) (.leaf (.eqB01 13 5383544556))))
            (.node (.node (.leaf (.eqDiag 15 2034041681)) (.leaf (.eqB00 15 (-636648844)))) (.node (.leaf (.eqB10 15 4330377204)) (.leaf (.eqB00 16 (-1332304110))))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.eqB10 16 2329784048)) (.node (.leaf (.eqB01 16 27565629)) (.leaf (.eqDiag 17 337130697))))
            (.node (.node (.leaf (.eqB00 17 (-45640357))) (.leaf (.eqB01 17 2345287012))) (.node (.leaf (.eqDiag 18 73330628)) (.leaf (.eqB00 18 (-2154200651))))))
            (.node
            (.node (.node (.leaf (.eqB10 18 3322463521)) (.leaf (.eqB01 18 1409182061))) (.node (.leaf (.eqDiag 20 37635403)) (.leaf (.eqB00 20 (-1514341271)))))
            (.node (.node (.leaf (.eqB00 21 253062990)) (.leaf (.eqB10 21 265445973))) (.node (.leaf (.eqSym 0 3 0 1428622213)) (.leaf (.eqSym 0 5 0 (-991871993)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 0 9 0 285724443)) (.leaf (.eqSym 0 15 0 (-97962666)))) (.node (.leaf (.eqSym 0 19 0 58004210)) (.leaf (.eqSym 0 21 0 (-20408889)))))
            (.node (.node (.leaf (.eqSym 1 2 1 364694108)) (.leaf (.eqSym 1 3 0 797250331))) (.node (.leaf (.eqSym 1 8 1 (-529553333))) (.leaf (.eqSym 1 11 0 (-602366917))))))
            (.node
            (.node (.node (.leaf (.eqSym 1 11 1 588980985)) (.leaf (.eqSym 1 14 0 635464000))) (.node (.leaf (.eqSym 1 19 0 (-523108112))) (.leaf (.eqSym 1 19 1 (-2126000882)))))
            (.node (.node (.leaf (.eqSym 1 20 0 328224698)) (.leaf (.eqSym 1 20 1 3099899922))) (.node (.leaf (.eqSym 1 21 1 (-1158885663))) (.leaf (.eqSym 2 3 0 (-7592780640)))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 2 3 1 21118982892)) (.node (.leaf (.eqSym 2 3 2 (-2745722539))) (.leaf (.eqSym 2 4 1 953504310))))
            (.node (.node (.leaf (.eqSym 2 4 2 (-1647129950))) (.leaf (.eqSym 2 5 0 14002501669))) (.node (.leaf (.eqSym 2 5 1 (-10685537366))) (.leaf (.eqSym 2 5 2 8567027240)))))
            (.node
            (.node (.node (.leaf (.eqSym 2 6 0 15994597225)) (.leaf (.eqSym 2 6 1 (-1376358290)))) (.node (.leaf (.eqSym 2 6 2 (-4096249683))) (.leaf (.eqSym 2 7 1 8977804825))))
            (.node (.node (.leaf (.eqSym 2 8 0 (-10606002929))) (.leaf (.eqSym 2 9 1 679529229))) (.node (.leaf (.eqSym 2 9 2 1803766990)) (.leaf (.eqSym 2 12 1 17140868465))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 2 13 1 (-19252789515))) (.leaf (.eqSym 2 14 0 7378727770))) (.node (.leaf (.eqSym 2 15 1 1748836351)) (.leaf (.eqSym 2 16 1 7950380445))))
            (.node (.node (.leaf (.eqSym 2 17 0 2834240528)) (.leaf (.eqSym 2 17 1 (-3027273788)))) (.node (.leaf (.eqSym 2 17 2 4685578170)) (.leaf (.eqSym 2 19 0 1399368094)))))
            (.node
            (.node (.node (.leaf (.eqSym 2 19 1 643808486)) (.leaf (.eqSym 2 19 2 (-1263971175)))) (.node (.leaf (.eqSym 2 20 1 (-4890494))) (.leaf (.eqSym 2 21 2 1162286088))))
            (.node (.node (.leaf (.eqSym 3 4 0 760223740)) (.leaf (.eqSym 3 4 2 4434530948))) (.node (.leaf (.eqSym 3 5 0 (-12992368758))) (.leaf (.eqSym 3 5 1 26968568032)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 3 5 2 (-12364934627))) (.node (.leaf (.eqSym 3 5 3 645016189)) (.leaf (.eqSym 3 8 2 (-36237571)))))
            (.node (.node (.leaf (.eqSym 3 8 3 2483047417)) (.leaf (.eqSym 3 9 0 (-1910827429)))) (.node (.leaf (.eqSym 3 9 1 (-24096192000))) (.leaf (.eqSym 3 10 0 34510136788)))))
            (.node
            (.node (.node (.leaf (.eqSym 3 10 3 (-7865962929))) (.leaf (.eqSym 3 11 0 (-24693536073)))) (.node (.leaf (.eqSym 3 11 2 11257165050)) (.leaf (.eqSym 3 12 3 3477094917))))
            (.node (.node (.leaf (.eqSym 3 13 1 8637234479)) (.leaf (.eqSym 3 14 0 (-3189894448)))) (.node (.leaf (.eqSym 3 15 1 1767803494)) (.leaf (.eqSym 3 16 2 (-8857816431)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 3 17 0 2161207223)) (.leaf (.eqSym 3 17 1 1690895607))) (.node (.leaf (.eqSym 3 18 0 (-334874461))) (.leaf (.eqSym 3 18 1 87748336))))
            (.node (.node (.leaf (.eqSym 3 18 2 (-3640489888))) (.leaf (.eqSym 3 19 1 (-2829325963)))) (.node (.leaf (.eqSym 3 19 2 6931129437)) (.leaf (.eqSym 3 19 3 1811813616)))))
            (.node
            (.node (.node (.leaf (.eqSym 3 20 2 (-469069458))) (.leaf (.eqSym 3 20 3 (-937269947)))) (.node (.leaf (.eqSym 3 21 3 (-513320840))) (.leaf (.eqSym 4 5 2 5365887819))))
            (.node (.node (.leaf (.eqSym 4 7 4 2672740203)) (.leaf (.eqSym 4 8 2 (-4182823905)))) (.node (.leaf (.eqSym 4 8 4 3695297889)) (.leaf (.eqSym 4 9 1 614563325)))))))))
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 4 9 4 (-23663209257))) (.node (.leaf (.eqSym 4 10 0 368460178)) (.leaf (.eqSym 4 10 4 21990452060))))
            (.node (.node (.leaf (.eqSym 4 11 2 1790566831)) (.leaf (.eqSym 4 13 1 (-521447670)))) (.node (.leaf (.eqSym 4 13 4 (-8636084447))) (.leaf (.eqSym 4 14 0 (-1478627445))))))
            (.node
            (.node (.node (.leaf (.eqSym 4 14 4 3777478336)) (.leaf (.eqSym 4 15 0 1521570160))) (.node (.leaf (.eqSym 4 17 0 (-290513280))) (.leaf (.eqSym 4 17 1 143398109))))
            (.node (.node (.leaf (.eqSym 4 17 2 (-242307578))) (.leaf (.eqSym 4 19 2 56077830))) (.node (.leaf (.eqSym 4 19 4 1775326795)) (.leaf (.eqSym 4 20 4 (-2207164875)))))))
            (.node
            (.node
            (.node (.leaf (.eqSym 5 6 1 (-8761625189))) (.node (.leaf (.eqSym 5 6 3 2347911714)) (.leaf (.eqSym 5 6 5 714574600))))
            (.node (.node (.leaf (.eqSym 5 8 0 4253054485)) (.leaf (.eqSym 5 8 1 24556237724))) (.node (.leaf (.eqSym 5 8 4 5730318438)) (.leaf (.eqSym 5 8 5 (-18139620364))))))
            (.node
            (.node (.node (.leaf (.eqSym 5 9 0 477930379)) (.leaf (.eqSym 5 9 2 4320791845))) (.node (.leaf (.eqSym 5 9 5 26014820939)) (.leaf (.eqSym 5 10 0 (-23400475298)))))
            (.node (.node (.leaf (.eqSym 5 10 1 (-32740601621))) (.leaf (.eqSym 5 10 3 714302892))) (.node (.leaf (.eqSym 5 10 5 (-19060523452))) (.leaf (.eqSym 5 11 0 13339888133)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 5 11 1 24912429879)) (.node (.leaf (.eqSym 5 11 2 (-482013536))) (.leaf (.eqSym 5 11 3 7457692758))))
            (.node (.node (.leaf (.eqSym 5 11 4 (-19788053133))) (.leaf (.eqSym 5 11 5 12889742707))) (.node (.leaf (.eqSym 5 12 0 5041032347)) (.leaf (.eqSym 5 12 1 (-4424412841))))))
            (.node
            (.node (.node (.leaf (.eqSym 5 12 3 (-12327551624))) (.leaf (.eqSym 5 13 1 2102869890))) (.node (.leaf (.eqSym 5 13 4 11437067466)) (.leaf (.eqSym 5 15 1 (-2694911707)))))
            (.node (.node (.leaf (.eqSym 5 15 2 (-2930728646))) (.leaf (.eqSym 5 16 1 447522329))) (.node (.leaf (.eqSym 5 16 4 8882839148)) (.leaf (.eqSym 5 16 5 (-4252779590)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 5 17 5 (-3598681967))) (.leaf (.eqSym 5 18 2 659930770))) (.node (.leaf (.eqSym 5 19 3 2452660448)) (.leaf (.eqSym 5 19 4 (-6262171920)))))
            (.node (.node (.leaf (.eqSym 5 19 5 4155904344)) (.leaf (.eqSym 6 7 1 (-10773990398)))) (.node (.leaf (.eqSym 6 7 5 (-8546115387))) (.leaf (.eqSym 6 8 3 (-14814227538))))))
            (.node
            (.node (.node (.leaf (.eqSym 6 8 5 19221522054)) (.leaf (.eqSym 6 9 0 (-661336501)))) (.node (.leaf (.eqSym 6 9 1 7937214744)) (.leaf (.eqSym 6 9 3 15371210176))))
            (.node (.node (.leaf (.eqSym 6 9 5 (-3618964595))) (.leaf (.eqSym 6 9 6 (-2461853324)))) (.node (.leaf (.eqSym 6 10 1 4074512632)) (.leaf (.eqSym 6 11 2 (-15898008155)))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 6 11 3 2817092827)) (.node (.leaf (.eqSym 6 11 5 (-7909257038))) (.leaf (.eqSym 6 12 0 1351073580))))
            (.node (.node (.leaf (.eqSym 6 12 3 8478454377)) (.leaf (.eqSym 6 13 0 (-832744095)))) (.node (.leaf (.eqSym 6 13 1 (-6601337198))) (.leaf (.eqSym 6 13 4 243495288)))))
            (.node
            (.node (.node (.leaf (.eqSym 6 13 6 2389654319)) (.leaf (.eqSym 6 14 0 333603578))) (.node (.leaf (.eqSym 6 14 2 11801758472)) (.leaf (.eqSym 6 14 3 (-7803494346)))))
            (.node (.node (.leaf (.eqSym 6 15 1 925901340)) (.leaf (.eqSym 6 15 3 2402122672))) (.node (.leaf (.eqSym 6 16 1 (-340628799))) (.leaf (.eqSym 6 16 3 (-4103246454)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 6 19 4 (-243495288))) (.leaf (.eqSym 6 19 5 1567389565))) (.node (.leaf (.eqSym 6 19 6 (-721623356))) (.leaf (.eqSym 6 20 6 274996330))))
            (.node (.node (.leaf (.eqSym 7 8 1 (-21091625025))) (.leaf (.eqSym 7 8 7 3418820772))) (.node (.leaf (.eqSym 7 9 4 2320094850)) (.leaf (.eqSym 7 9 6 (-9631559869))))))
            (.node
            (.node (.node (.leaf (.eqSym 7 10 0 (-1497411513))) (.leaf (.eqSym 7 10 1 21307905545))) (.node (.leaf (.eqSym 7 10 2 (-9662961902))) (.leaf (.eqSym 7 10 3 18189012315))))
            (.node (.node (.leaf (.eqSym 7 10 4 (-14128929315))) (.leaf (.eqSym 7 10 6 5452945510))) (.node (.leaf (.eqSym 7 10 7 (-11810848370))) (.leaf (.eqSym 7 11 0 162753173)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 7 11 4 391879568)) (.node (.leaf (.eqSym 7 11 7 11228878096)) (.leaf (.eqSym 7 12 1 (-5325779066)))))
            (.node (.node (.leaf (.eqSym 7 12 6 1982442020)) (.leaf (.eqSym 7 13 1 673315373))) (.node (.leaf (.eqSym 7 13 3 (-2083336026))) (.leaf (.eqSym 7 14 0 381372931)))))
            (.node
            (.node (.node (.leaf (.eqSym 7 14 3 (-2809090469))) (.leaf (.eqSym 7 14 7 (-3333079853)))) (.node (.leaf (.eqSym 7 15 1 (-680649810))) (.leaf (.eqSym 7 15 7 1717780216))))
            (.node (.node (.leaf (.eqSym 7 16 3 2172852883)) (.leaf (.eqSym 7 17 3 635497800))) (.node (.leaf (.eqSym 7 17 4 (-2015241403))) (.leaf (.eqSym 7 17 5 1675380383))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 7 17 6 703306122)) (.leaf (.eqSym 7 17 7 586986013))) (.node (.leaf (.eqSym 7 18 5 1512519002)) (.leaf (.eqSym 7 18 6 2965882565))))
            (.node (.node (.leaf (.eqSym 7 18 7 (-6480308114))) (.leaf (.eqSym 7 19 6 (-4694003649)))) (.node (.leaf (.eqSym 7 19 7 5124525282)) (.leaf (.eqSym 8 9 3 (-19194256769))))))
            (.node
            (.node (.node (.leaf (.eqSym 8 9 5 11110141353)) (.leaf (.eqSym 8 10 0 (-145792460)))) (.node (.leaf (.eqSym 8 10 2 19174549415)) (.leaf (.eqSym 8 10 7 4924949095))))
            (.node (.node (.leaf (.eqSym 8 10 8 20035939082)) (.leaf (.eqSym 8 11 0 (-232342006)))) (.node (.leaf (.eqSym 8 11 2 (-23152601234))) (.leaf (.eqSym 8 11 4 9038470058))))))))))
      (.node
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 8 11 8 (-21575612681))) (.node (.leaf (.eqSym 8 12 1 (-2911162561))) (.leaf (.eqSym 8 12 6 (-6205511086)))))
            (.node (.node (.leaf (.eqSym 8 13 1 3586254849)) (.leaf (.eqSym 8 13 3 15553769320))) (.node (.leaf (.eqSym 8 13 4 (-15283010305))) (.leaf (.eqSym 8 14 2 (-2550403306))))))
            (.node
            (.node (.node (.leaf (.eqSym 8 14 7 (-807355111))) (.leaf (.eqSym 8 16 4 (-283090979)))) (.node (.leaf (.eqSym 8 16 5 6806263752)) (.leaf (.eqSym 8 16 8 8395627353))))
            (.node (.node (.leaf (.eqSym 8 19 6 (-4247693307))) (.leaf (.eqSym 8 19 7 544919874))) (.node (.leaf (.eqSym 8 19 8 (-9219153409))) (.leaf (.eqSym 8 20 7 2324637508))))))
            (.node
            (.node
            (.node (.leaf (.eqSym 8 20 8 4151085256)) (.node (.leaf (.eqSym 9 10 0 3894624562)) (.leaf (.eqSym 9 10 1 4212832594))))
            (.node (.node (.leaf (.eqSym 9 10 3 (-7497522693))) (.leaf (.eqSym 9 10 6 6804146985))) (.node (.leaf (.eqSym 9 10 9 (-9610791727))) (.leaf (.eqSym 9 11 0 (-2235910977))))))
            (.node
            (.node (.node (.leaf (.eqSym 9 11 1 (-7335767844))) (.leaf (.eqSym 9 11 5 2242178766))) (.node (.leaf (.eqSym 9 11 8 (-1822310694))) (.leaf (.eqSym 9 11 9 6630868562))))
            (.node (.node (.leaf (.eqSym 9 12 1 4077762928)) (.leaf (.eqSym 9 12 9 (-130864152)))) (.node (.leaf (.eqSym 9 13 1 (-161281654))) (.leaf (.eqSym 9 13 4 1448205800)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 9 14 7 1090411661)) (.node (.leaf (.eqSym 9 15 5 860956686)) (.leaf (.eqSym 9 16 8 (-10540696253)))))
            (.node (.node (.leaf (.eqSym 9 18 7 (-6568721776))) (.leaf (.eqSym 9 18 8 9358389213))) (.node (.leaf (.eqSym 9 18 9 6039309554)) (.leaf (.eqSym 9 19 7 729237466)))))
            (.node
            (.node (.node (.leaf (.eqSym 9 19 8 1821799444)) (.leaf (.eqSym 9 19 9 (-4417961194)))) (.node (.leaf (.eqSym 9 20 8 842040023)) (.leaf (.eqSym 9 20 9 (-1899725315)))))
            (.node (.node (.leaf (.eqSym 10 11 0 1282729675)) (.leaf (.eqSym 10 11 2 13239179503))) (.node (.leaf (.eqSym 10 11 5 (-3262470040))) (.leaf (.eqSym 10 11 7 (-2309360850)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 10 11 9 10580824531)) (.leaf (.eqSym 10 11 10 (-2002251704)))) (.node (.leaf (.eqSym 10 12 1 (-709449251))) (.leaf (.eqSym 10 12 3 13731569889))))
            (.node (.node (.leaf (.eqSym 10 12 7 8234685469)) (.leaf (.eqSym 10 13 3 (-10817910292)))) (.node (.leaf (.eqSym 10 13 8 2384493286)) (.leaf (.eqSym 10 13 9 (-4246910718))))))
            (.node
            (.node (.node (.leaf (.eqSym 10 14 7 10683925693)) (.leaf (.eqSym 10 15 7 (-6896414696)))) (.node (.leaf (.eqSym 10 15 8 (-3950277623))) (.leaf (.eqSym 10 16 6 (-6412540894)))))
            (.node (.node (.leaf (.eqSym 10 16 9 (-6833978009))) (.leaf (.eqSym 10 16 10 (-5424744987)))) (.node (.leaf (.eqSym 10 17 8 (-1494317217))) (.leaf (.eqSym 10 17 9 8298187989))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 10 17 10 4812157823)) (.node (.leaf (.eqSym 10 18 7 (-847451942))) (.leaf (.eqSym 10 18 8 3470699425))))
            (.node (.node (.leaf (.eqSym 10 18 9 (-7112731814))) (.leaf (.eqSym 10 18 10 2631964517))) (.node (.leaf (.eqSym 10 19 8 10188637576)) (.leaf (.eqSym 10 20 9 (-6886116590))))))
            (.node
            (.node (.node (.leaf (.eqSym 10 20 10 1261050883)) (.leaf (.eqSym 11 12 3 (-2810087777)))) (.node (.leaf (.eqSym 11 12 4 (-10352054157))) (.leaf (.eqSym 11 12 6 1117623580))))
            (.node (.node (.leaf (.eqSym 11 12 9 (-2097392677))) (.leaf (.eqSym 11 12 11 (-617528063)))) (.node (.leaf (.eqSym 11 13 4 8142473197)) (.leaf (.eqSym 11 13 9 (-7637605593)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 11 13 10 7204719036)) (.leaf (.eqSym 11 14 4 (-1572096578)))) (.node (.leaf (.eqSym 11 14 7 (-9609148267))) (.leaf (.eqSym 11 14 9 (-1874070190)))))
            (.node (.node (.leaf (.eqSym 11 14 11 2051700796)) (.leaf (.eqSym 11 15 5 3518088875))) (.node (.leaf (.eqSym 11 15 8 14343789637)) (.leaf (.eqSym 11 15 11 (-908638908))))))
            (.node
            (.node (.node (.leaf (.eqSym 11 16 6 1040980721)) (.leaf (.eqSym 11 16 8 (-1375077305)))) (.node (.leaf (.eqSym 11 16 10 15451747348)) (.leaf (.eqSym 11 17 7 (-408534300)))))
            (.node (.node (.leaf (.eqSym 11 17 8 1490819476)) (.leaf (.eqSym 11 17 10 (-15825525504)))) (.node (.leaf (.eqSym 11 17 11 (-3721999378))) (.leaf (.eqSym 11 18 9 2083933377)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 11 18 11 (-2396864786))) (.node (.leaf (.eqSym 11 19 9 (-8199544080))) (.leaf (.eqSym 11 19 10 2402671919))))
            (.node (.node (.leaf (.eqSym 11 19 11 6305334101)) (.leaf (.eqSym 11 20 10 4528153855))) (.node (.leaf (.eqSym 11 20 11 (-3243016153))) (.leaf (.eqSym 11 21 11 (-11042169))))))
            (.node
            (.node (.node (.leaf (.eqSym 12 13 4 (-10636653))) (.leaf (.eqSym 12 13 9 8370325185))) (.node (.leaf (.eqSym 12 13 10 (-6889219577))) (.leaf (.eqSym 12 13 12 471295940))))
            (.node (.node (.leaf (.eqSym 12 15 7 (-1620481116))) (.leaf (.eqSym 12 16 8 (-700883471)))) (.node (.leaf (.eqSym 12 17 11 6300593929)) (.leaf (.eqSym 12 18 9 518165472))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 12 18 11 (-13261239351))) (.leaf (.eqSym 12 19 11 9417086981))) (.node (.leaf (.eqSym 12 20 11 (-2316327915))) (.leaf (.eqSym 13 14 6 4143323761))))
            (.node (.node (.leaf (.eqSym 13 14 7 2909063079)) (.leaf (.eqSym 13 15 7 (-6901730489)))) (.node (.leaf (.eqSym 13 15 10 (-5391952104))) (.leaf (.eqSym 13 16 8 116749324)))))
            (.node
            (.node (.node (.leaf (.eqSym 13 16 9 5257176792)) (.leaf (.eqSym 13 16 13 (-1518115179)))) (.node (.leaf (.eqSym 13 17 12 738020415)) (.leaf (.eqSym 13 18 12 8280860798))))
            (.node (.node (.leaf (.eqSym 13 19 12 (-10228332290))) (.leaf (.eqSym 13 19 13 508889516))) (.node (.leaf (.eqSym 13 20 12 2890916508)) (.leaf (.eqSym 14 15 8 3693466224)))))))))
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 14 15 11 (-1699485236))) (.node (.leaf (.eqSym 14 15 13 3406940988)) (.leaf (.eqSym 14 15 14 (-1995376991)))))
            (.node (.node (.leaf (.eqSym 14 17 14 (-309463101))) (.leaf (.eqSym 14 18 14 (-395622473)))) (.node (.leaf (.eqSym 14 20 13 (-987651448))) (.leaf (.eqSym 14 20 14 692263351)))))
            (.node
            (.node (.node (.leaf (.eqSym 14 21 14 246785337)) (.leaf (.eqSym 15 16 10 (-893857866)))) (.node (.leaf (.eqSym 15 16 12 (-2631519731))) (.leaf (.eqSym 15 16 14 (-2182474129)))))
            (.node (.node (.leaf (.eqSym 15 16 15 3088477155)) (.leaf (.eqSym 15 17 14 1243214342))) (.node (.leaf (.eqSym 15 18 14 2319134870)) (.leaf (.eqSym 15 18 15 (-1415882715)))))))
            (.node
            (.node
            (.node (.leaf (.eqSym 15 19 14 (-289318299))) (.node (.leaf (.eqSym 15 20 14 809515081)) (.leaf (.eqSym 15 20 15 (-405261477)))))
            (.node (.node (.leaf (.eqSym 15 21 15 (-286482416))) (.leaf (.eqSym 16 19 14 939221573))) (.node (.leaf (.eqSym 16 19 15 (-1369408500))) (.leaf (.eqSym 16 19 16 (-1303579739))))))
            (.node
            (.node (.node (.leaf (.eqSym 16 20 15 (-1007220533))) (.leaf (.eqSym 16 20 16 1850445160))) (.node (.leaf (.eqSym 17 18 15 55455385)) (.leaf (.eqSym 17 18 16 794817858))))
            (.node (.node (.leaf (.eqSym 17 18 17 775810518)) (.leaf (.eqSym 17 19 15 (-63549780)))) (.node (.leaf (.eqSym 17 19 16 198572346)) (.leaf (.eqSym 17 19 17 (-887555359))))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 18 19 17 2527289994)) (.node (.leaf (.eqSym 18 19 18 1113806312)) (.leaf (.eqSym 18 20 17 (-127330099)))))
            (.node (.node (.leaf (.eqSym 18 20 18 (-1885656246))) (.leaf (.eqSym 18 21 18 123099938))) (.node (.leaf (.eqSym 19 20 18 255905279)) (.leaf (.eqSym 19 20 19 733859607)))))
            (.node
            (.node (.node (.leaf (.eqSym 19 21 19 (-74310711))) (.leaf (.eqSym 20 21 20 20537564))) (.node (.leaf (.ubHGe0 2 0 0 33304314918)) (.leaf (.ubHLePj 2 0 1 100089462334))))
            (.node (.node (.leaf (.ubHMcc 2 0 2 77729810861)) (.leaf (.ubHMcc 2 0 11 5144426810))) (.node (.leaf (.ubHMcc 2 0 17 7321596682)) (.leaf (.ubHLePj 2 1 0 10348010349))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHMcc 2 1 1 26464966187)) (.leaf (.ubHMcc 2 1 10 7410190532))) (.node (.leaf (.ubHMcc 2 1 19 975025070)) (.leaf (.ubHLePi 2 2 0 824779254))))
            (.node (.node (.leaf (.ubHMcc 2 2 7 3581662904)) (.leaf (.ubHMcc 2 2 17 4377450472))) (.node (.leaf (.ubHLePi 2 2 19 668748981)) (.leaf (.ubHLePi 3 0 16 305551179)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 3 0 18 17474145)) (.leaf (.ubHLePj 3 1 0 8892250906))) (.node (.leaf (.ubHLePi 3 3 2 3123482259)) (.leaf (.ubHGe0 4 0 0 772692905))))
            (.node (.node (.leaf (.ubHLePj 4 0 1 1412027033)) (.leaf (.ubHLePj 4 1 0 716990546))) (.node (.leaf (.ubHLePi 4 4 1 215098220)) (.leaf (.ubHLePi 4 4 17 705502134))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHGe0 5 0 0 3068001245)) (.node (.leaf (.ubHLePj 5 0 1 5396374156)) (.leaf (.ubHGe0 5 0 5 92381026))))
            (.node (.node (.leaf (.ubHGe0 5 0 14 1478629298)) (.leaf (.ubHGe0 5 0 15 450531715))) (.node (.leaf (.ubHLePj 5 1 1 15157207907)) (.leaf (.ubHLePi 5 5 0 1331902601)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 5 5 11 55339815)) (.leaf (.ubHLePj 6 0 2 13893082512))) (.node (.leaf (.ubHLePi 6 6 0 777566867)) (.leaf (.ubHLePj 6 6 14 27150824))))
            (.node (.node (.leaf (.ubHGe0 6 6 15 285891660)) (.leaf (.ubHGe0 7 0 0 2750010514))) (.node (.leaf (.ubHLePj 7 0 1 3243154881)) (.leaf (.ubHLePj 7 1 0 6541634709))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 7 5 0 2071053074)) (.leaf (.ubHLePj 7 7 1 388580300))) (.node (.leaf (.ubHLePj 7 7 2 799244018)) (.leaf (.ubHGe0 8 0 0 1982166256))))
            (.node (.node (.leaf (.ubHLePj 8 1 0 2338093067)) (.leaf (.ubHMcc 9 0 10 1068641473))) (.node (.leaf (.ubHLePi 9 9 0 3673542128)) (.leaf (.ubHGe0 10 0 0 2183663467)))))
            (.node
            (.node (.node (.leaf (.ubHLePj 10 0 1 15023406461)) (.leaf (.ubHLePj 10 0 11 20275541))) (.node (.leaf (.ubHLePi 10 6 0 166352572)) (.leaf (.ubHMcc 10 10 2 651554419))))
            (.node (.node (.leaf (.ubHGe0 11 0 0 2445854581)) (.leaf (.ubHLePj 11 1 0 11452408000))) (.node (.leaf (.ubHLePi 11 11 10 28278574)) (.leaf (.ubHGe0 12 0 0 6375570585)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePj 12 0 1 9505926252)) (.node (.leaf (.ubHLePi 12 0 7 2141701776)) (.leaf (.ubHLePj 12 1 0 11372537555))))
            (.node (.node (.leaf (.ubHLePi 12 12 2 437552644)) (.leaf (.ubHLePi 12 12 3 54895811))) (.node (.leaf (.ubHLePi 13 0 7 9746382)) (.leaf (.ubHLePi 13 13 0 678960597)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 14 0 0 1340631315)) (.leaf (.ubHLePj 14 0 1 1823485880))) (.node (.leaf (.ubHLePj 14 0 2 3429946161)) (.leaf (.ubHLePj 14 1 0 2722147431))))
            (.node (.node (.leaf (.ubHLePi 14 14 0 1114583163)) (.leaf (.ubHGe0 14 14 2 241817908))) (.node (.leaf (.ubHLePj 15 0 1 2067300184)) (.leaf (.ubHLePj 15 2 0 4443571692))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePj 16 1 1 3897567748)) (.leaf (.ubHLePi 16 16 0 1285944691))) (.node (.leaf (.ubHGe0 16 16 5 8757660)) (.leaf (.ubHLePj 17 0 2 4556629225))))
            (.node (.node (.leaf (.ubHLePj 17 0 3 1526155674)) (.leaf (.ubHLePj 17 1 0 2658140954))) (.node (.leaf (.ubHLePi 17 16 0 87926947)) (.leaf (.ubHGe0 19 0 0 4194540756)))))
            (.node
            (.node (.node (.leaf (.ubHLePj 19 0 1 1954465670)) (.leaf (.ubHLePj 19 1 0 5016167280))) (.node (.leaf (.ubHLePi 19 19 0 92118609)) (.leaf (.ubHLePj 20 0 1 160248852))))
            (.node (.node (.leaf (.ubHLePi 20 15 0 8800627)) (.leaf (.ubHLePi 21 21 0 6767201))) (.node (.leaf (.ubHLePi 0 0 6 17094)) (.leaf (.ubHGe0 0 0 5 96010)))))))))))
    (.node
      (.node
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 0 0 4 225582)) (.node (.leaf (.ubHGe0 0 0 3 283693)) (.leaf (.ubHLePi 0 0 2 201330))))
            (.node (.node (.leaf (.ubHGe0 0 0 1 76422)) (.leaf (.ubHLePi 0 0 0 12119))) (.node (.leaf (.ubHGe0 1 0 6 21937)) (.leaf (.ubHGe0 1 1 5 5115)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 1 0 5 127820)) (.leaf (.ubHLePi 1 1 4 23863))) (.node (.leaf (.ubHGe0 1 0 4 311133)) (.leaf (.ubHGe0 1 1 3 44733))))
            (.node (.node (.leaf (.ubHLePi 1 0 3 404854)) (.leaf (.ubHLePi 1 1 2 42093))) (.node (.leaf (.ubHGe0 1 0 2 296935)) (.leaf (.ubHGe0 1 1 1 19873))))))
            (.node
            (.node
            (.node (.leaf (.ubHLePi 1 0 1 116361)) (.node (.leaf (.ubHLePi 1 1 0 3765)) (.leaf (.ubHGe0 1 0 0 19030))))
            (.node (.node (.leaf (.ubHGe0 2 0 6 22212)) (.leaf (.ubHGe0 2 1 5 25303))) (.node (.leaf (.ubHGe0 2 2 4 2961)) (.leaf (.ubHLePi 2 0 5 147889)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 2 1 4 123409)) (.leaf (.ubHLePi 2 2 3 11075))) (.node (.leaf (.ubHGe0 2 0 4 404249)) (.leaf (.ubHGe0 2 1 3 241480))))
            (.node (.node (.leaf (.ubHGe0 2 2 2 15594)) (.leaf (.ubHLePi 2 0 3 582824))) (.node (.leaf (.ubHLePi 2 1 2 236838)) (.leaf (.ubHLePi 2 2 1 9794)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHGe0 2 0 2 468610)) (.node (.leaf (.ubHGe0 2 1 1 116380)) (.leaf (.ubHGe0 2 2 0 2314))))
            (.node (.node (.leaf (.ubHLePi 2 0 1 199578)) (.leaf (.ubHLePi 2 1 0 22914))) (.node (.leaf (.ubHGe0 3 0 6 7421)) (.leaf (.ubHLePi 3 1 5 2658)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 3 2 4 640)) (.leaf (.ubHGe0 3 3 3 243))) (.node (.leaf (.ubHLePi 3 0 5 38280)) (.leaf (.ubHGe0 3 1 4 10645))))
            (.node (.node (.leaf (.ubHLePi 3 2 3 3139)) (.leaf (.ubHGe0 3 0 4 83455))) (.node (.leaf (.ubHLePi 3 1 3 16084)) (.leaf (.ubHGe0 3 2 2 5456))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 3 3 1 639)) (.leaf (.ubHLePi 3 0 3 98629))) (.node (.leaf (.ubHGe0 3 1 2 10919)) (.leaf (.ubHLePi 3 2 1 4073))))
            (.node (.node (.leaf (.ubHLePi 3 3 0 201)) (.leaf (.ubHGe0 3 0 2 66835))) (.node (.leaf (.ubHLePi 3 1 1 2886)) (.leaf (.ubHGe0 3 2 0 1115)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 3 0 1 24699)) (.leaf (.ubHGe0 3 1 0 63))) (.node (.leaf (.ubHGe0 3 0 0 3899)) (.leaf (.ubHLePi 4 0 6 4023))))
            (.node (.node (.leaf (.ubHLePi 4 1 5 3044)) (.leaf (.ubHLePi 4 2 4 417))) (.node (.leaf (.ubHGe0 4 3 3 24)) (.leaf (.ubHGe0 4 0 5 25272))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHGe0 4 1 4 15004)) (.node (.leaf (.ubHGe0 4 2 3 1565)) (.leaf (.ubHLePi 4 3 2 72))))
            (.node (.node (.leaf (.ubHLePi 4 0 4 66069)) (.leaf (.ubHLePi 4 1 3 29712))) (.node (.leaf (.ubHLePi 4 2 2 2205)) (.leaf (.ubHGe0 4 3 1 72)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 4 4 0 2)) (.leaf (.ubHGe0 4 0 3 92050))) (.node (.leaf (.ubHGe0 4 1 2 29512)) (.leaf (.ubHGe0 4 2 1 1381))))
            (.node (.node (.leaf (.ubHLePi 4 3 0 24)) (.leaf (.ubHLePi 4 0 2 72096))) (.node (.leaf (.ubHLePi 4 1 1 14690)) (.leaf (.ubHLePi 4 2 0 325))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 4 0 1 30099)) (.leaf (.ubHGe0 4 1 0 2930))) (.node (.leaf (.ubHLePi 4 0 0 5232)) (.leaf (.ubHGe0 5 0 6 1914))))
            (.node (.node (.leaf (.ubHLePi 5 1 5 182)) (.leaf (.ubHLePi 5 2 4 1519))) (.node (.leaf (.ubHLePi 5 3 3 720)) (.leaf (.ubHLePi 5 4 2 51)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 5 5 1 3)) (.leaf (.ubHLePi 5 0 5 10323))) (.node (.leaf (.ubHGe0 5 1 4 3632)) (.leaf (.ubHGe0 5 2 3 7605))))
            (.node (.node (.leaf (.ubHGe0 5 3 2 2214)) (.leaf (.ubHGe0 5 4 1 93))) (.node (.leaf (.ubHGe0 5 0 4 22052)) (.leaf (.ubHLePi 5 1 3 13811)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 5 2 2 13719)) (.node (.leaf (.ubHLePi 5 3 1 2266)) (.leaf (.ubHLePi 5 4 0 43))))
            (.node (.node (.leaf (.ubHLePi 5 0 3 22889)) (.leaf (.ubHGe0 5 1 2 21465))) (.node (.leaf (.ubHGe0 5 2 1 10701)) (.leaf (.ubHGe0 5 3 0 771)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 5 0 2 10892)) (.leaf (.ubHLePi 5 1 1 15116))) (.node (.leaf (.ubHLePi 5 2 0 3067)) (.leaf (.ubHLePi 5 0 1 1191))))
            (.node (.node (.leaf (.ubHGe0 5 1 0 4012)) (.leaf (.ubHLePi 5 0 0 455))) (.node (.leaf (.ubHGe0 6 0 6 4173)) (.leaf (.ubHGe0 6 1 5 7517))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 6 2 4 6879)) (.leaf (.ubHGe0 6 3 3 2994))) (.node (.leaf (.ubHGe0 6 4 2 473)) (.leaf (.ubHGe0 6 5 1 24))))
            (.node (.node (.leaf (.ubHLePi 6 0 5 30174)) (.leaf (.ubHLePi 6 1 4 47975))) (.node (.leaf (.ubHLePi 6 2 3 34233)) (.leaf (.ubHLePi 6 3 2 10218)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 6 4 1 1009)) (.leaf (.ubHLePi 6 5 0 25))) (.node (.leaf (.ubHGe0 6 0 4 92788)) (.leaf (.ubHGe0 6 1 3 122267))))
            (.node (.node (.leaf (.ubHGe0 6 2 2 62782)) (.leaf (.ubHGe0 6 3 1 11537))) (.node (.leaf (.ubHGe0 6 4 0 536)) (.leaf (.ubHLePi 6 0 3 154392)))))))))
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 6 1 2 154798)) (.node (.leaf (.ubHLePi 6 2 1 50447)) (.leaf (.ubHLePi 6 3 0 4313))))
            (.node (.node (.leaf (.ubHGe0 6 0 2 145727)) (.leaf (.ubHGe0 6 1 1 97141))) (.node (.leaf (.ubHGe0 6 2 0 15019)) (.leaf (.ubHLePi 6 0 1 73605)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 6 1 0 24152)) (.leaf (.ubHGe0 6 0 0 15483))) (.node (.leaf (.ubHGe0 7 0 6 667)) (.leaf (.ubHLePi 7 1 5 2350))))
            (.node (.node (.leaf (.ubHLePi 7 2 4 5679)) (.leaf (.ubHLePi 7 3 3 4819))) (.node (.leaf (.ubHLePi 7 4 2 1486)) (.leaf (.ubHLePi 7 5 1 184))))))
            (.node
            (.node
            (.node (.leaf (.ubHLePi 7 6 0 7)) (.node (.leaf (.ubHLePi 7 0 5 1426)) (.leaf (.ubHGe0 7 1 4 21280))))
            (.node (.node (.leaf (.ubHGe0 7 2 3 34437)) (.leaf (.ubHGe0 7 3 2 18871))) (.node (.leaf (.ubHGe0 7 4 1 3569)) (.leaf (.ubHLePi 7 0 4 6759)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 7 1 3 71555)) (.leaf (.ubHLePi 7 2 2 74462))) (.node (.leaf (.ubHLePi 7 3 1 24165)) (.leaf (.ubHLePi 7 4 0 2116))))
            (.node (.node (.leaf (.ubHGe0 7 0 3 30905)) (.leaf (.ubHGe0 7 1 2 113304))) (.node (.leaf (.ubHGe0 7 2 1 69027)) (.leaf (.ubHGe0 7 3 0 10146)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 7 0 2 48476)) (.node (.leaf (.ubHLePi 7 1 1 85615)) (.leaf (.ubHLePi 7 2 0 23343))))
            (.node (.node (.leaf (.ubHGe0 7 0 1 34457)) (.leaf (.ubHGe0 7 1 0 24941))) (.node (.leaf (.ubHLePi 7 0 0 9368)) (.leaf (.ubHGe0 8 0 6 1311)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 8 1 5 5519)) (.leaf (.ubHGe0 8 2 4 8411))) (.node (.leaf (.ubHGe0 8 3 3 5020)) (.leaf (.ubHGe0 8 4 2 1324))))
            (.node (.node (.leaf (.ubHGe0 8 5 1 196)) (.leaf (.ubHGe0 8 6 0 5))) (.node (.leaf (.ubHLePi 8 0 5 12302)) (.leaf (.ubHLePi 8 1 4 41244))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 8 2 3 45342)) (.leaf (.ubHLePi 8 3 2 19007))) (.node (.leaf (.ubHLePi 8 4 1 3348)) (.leaf (.ubHLePi 8 5 0 215))))
            (.node (.node (.leaf (.ubHGe0 8 0 4 47753)) (.leaf (.ubHGe0 8 1 3 119413))) (.node (.leaf (.ubHGe0 8 2 2 90357)) (.leaf (.ubHGe0 8 3 1 24062)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 8 4 0 2061)) (.leaf (.ubHLePi 8 0 3 96860))) (.node (.leaf (.ubHLePi 8 1 2 168661)) (.leaf (.ubHLePi 8 2 1 79244))))
            (.node (.node (.leaf (.ubHLePi 8 3 0 10113)) (.leaf (.ubHGe0 8 0 2 108034))) (.node (.leaf (.ubHGe0 8 1 1 116853)) (.leaf (.ubHGe0 8 2 0 25843))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 8 0 1 62915)) (.node (.leaf (.ubHLePi 8 1 0 31889)) (.leaf (.ubHGe0 9 0 6 79))))
            (.node (.node (.leaf (.ubHGe0 9 1 5 745)) (.leaf (.ubHGe0 9 2 4 2074))) (.node (.leaf (.ubHGe0 9 3 3 2698)) (.leaf (.ubHGe0 9 4 2 1260)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 9 5 1 265)) (.leaf (.ubHGe0 9 6 0 63))) (.node (.leaf (.ubHLePi 9 0 5 1195)) (.leaf (.ubHLePi 9 1 4 7348))))
            (.node (.node (.leaf (.ubHLePi 9 2 3 15325)) (.leaf (.ubHLePi 9 3 2 12248))) (.node (.leaf (.ubHLePi 9 4 1 3543)) (.leaf (.ubHLePi 9 5 0 545))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 9 0 4 6322)) (.leaf (.ubHGe0 9 1 3 28169))) (.node (.leaf (.ubHGe0 9 2 2 38798)) (.leaf (.ubHGe0 9 3 1 18067))))
            (.node (.node (.leaf (.ubHGe0 9 4 0 2841)) (.leaf (.ubHLePi 9 0 3 16836))) (.node (.leaf (.ubHLePi 9 1 2 50884)) (.leaf (.ubHLePi 9 2 1 41319)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 9 3 0 9134)) (.leaf (.ubHGe0 9 0 2 23974))) (.node (.leaf (.ubHGe0 9 1 1 43539)) (.leaf (.ubHGe0 9 2 0 16168))))
            (.node (.node (.leaf (.ubHLePi 9 0 1 17342)) (.leaf (.ubHLePi 9 1 0 14358))) (.node (.leaf (.ubHGe0 9 0 0 5017)) (.leaf (.ubHGe0 10 0 6 307)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHGe0 10 1 5 2515)) (.node (.leaf (.ubHGe0 10 2 4 6107)) (.leaf (.ubHGe0 10 3 3 5417))))
            (.node (.node (.leaf (.ubHGe0 10 4 2 1817)) (.leaf (.ubHGe0 10 5 1 207))) (.node (.leaf (.ubHLePi 10 0 5 4029)) (.leaf (.ubHLePi 10 1 4 23014)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 10 2 3 37968)) (.leaf (.ubHLePi 10 3 2 22219))) (.node (.leaf (.ubHLePi 10 4 1 4546)) (.leaf (.ubHGe0 10 5 0 340))))
            (.node (.node (.leaf (.ubHGe0 10 0 4 20116)) (.leaf (.ubHGe0 10 1 3 78560))) (.node (.leaf (.ubHGe0 10 2 2 84940)) (.leaf (.ubHGe0 10 3 1 29829))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 10 4 0 1645)) (.leaf (.ubHLePi 10 0 3 49721))) (.node (.leaf (.ubHLePi 10 1 2 127242)) (.leaf (.ubHLePi 10 2 1 81891))))
            (.node (.node (.leaf (.ubHLePi 10 3 0 11830)) (.leaf (.ubHGe0 10 0 2 65161))) (.node (.leaf (.ubHGe0 10 1 1 98966)) (.leaf (.ubHGe0 10 2 0 28046)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 10 0 1 43445)) (.leaf (.ubHLePi 10 1 0 29517))) (.node (.leaf (.ubHLePi 11 0 6 85)) (.leaf (.ubHLePi 11 1 5 755))))
            (.node (.node (.leaf (.ubHLePi 11 2 4 3080)) (.leaf (.ubHLePi 11 3 3 2726))) (.node (.leaf (.ubHGe0 11 4 2 777)) (.leaf (.ubHGe0 11 5 1 1407))))))))))
      (.node
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHGe0 11 6 0 504)) (.node (.leaf (.ubHGe0 11 0 5 1161)) (.leaf (.ubHGe0 11 1 4 9414))))
            (.node (.node (.leaf (.ubHGe0 11 2 3 19308)) (.leaf (.ubHGe0 11 3 2 4995))) (.node (.leaf (.ubHLePi 11 4 1 7716)) (.leaf (.ubHLePi 11 5 0 3916)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 11 0 4 7182)) (.leaf (.ubHLePi 11 1 3 36125))) (.node (.leaf (.ubHLePi 11 2 2 34723)) (.leaf (.ubHGe0 11 3 1 9115))))
            (.node (.node (.leaf (.ubHGe0 11 4 0 12297)) (.leaf (.ubHGe0 11 0 3 20513))) (.node (.leaf (.ubHGe0 11 1 2 56393)) (.leaf (.ubHGe0 11 2 1 14049))))))
            (.node
            (.node
            (.node (.leaf (.ubHLePi 11 3 0 17618)) (.node (.leaf (.ubHLePi 11 0 2 28079)) (.leaf (.ubHLePi 11 1 1 33862))))
            (.node (.node (.leaf (.ubHGe0 11 2 0 8594)) (.leaf (.ubHGe0 11 0 1 17236))) (.node (.leaf (.ubHGe0 11 1 0 3444)) (.leaf (.ubHLePi 11 0 0 3339)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 12 0 6 17)) (.leaf (.ubHGe0 12 1 5 67))) (.node (.leaf (.ubHGe0 12 2 4 249)) (.leaf (.ubHLePi 12 3 3 252))))
            (.node (.node (.leaf (.ubHLePi 12 4 2 887)) (.leaf (.ubHGe0 12 5 1 121))) (.node (.leaf (.ubHGe0 12 6 0 31)) (.leaf (.ubHLePi 12 0 5 134)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 12 1 4 765)) (.node (.leaf (.ubHLePi 12 2 3 181)) (.leaf (.ubHGe0 12 3 2 4143))))
            (.node (.node (.leaf (.ubHGe0 12 4 1 1363)) (.leaf (.ubHLePi 12 5 0 266))) (.node (.leaf (.ubHGe0 12 0 4 642)) (.leaf (.ubHGe0 12 1 3 1555)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 12 2 2 5754)) (.leaf (.ubHLePi 12 3 1 6913))) (.node (.leaf (.ubHLePi 12 4 0 166)) (.leaf (.ubHLePi 12 0 3 1256))))
            (.node (.node (.leaf (.ubHGe0 12 1 2 2277)) (.leaf (.ubHGe0 12 2 1 10556))) (.node (.leaf (.ubHGe0 12 3 0 2654)) (.leaf (.ubHGe0 12 0 2 306))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 12 1 1 6280)) (.leaf (.ubHLePi 12 2 0 4620))) (.node (.leaf (.ubHGe0 12 0 1 1123)) (.leaf (.ubHGe0 12 1 0 3054))))
            (.node (.node (.leaf (.ubHLePi 12 0 0 684)) (.leaf (.ubHGe0 13 0 6 7))) (.node (.leaf (.ubHGe0 13 1 5 116)) (.leaf (.ubHGe0 13 2 4 253)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 13 3 3 641)) (.leaf (.ubHGe0 13 4 2 1239))) (.node (.leaf (.ubHGe0 13 5 1 180)) (.leaf (.ubHLePi 13 6 0 54))))
            (.node (.node (.leaf (.ubHLePi 13 0 5 148)) (.leaf (.ubHLePi 13 1 4 933))) (.node (.leaf (.ubHLePi 13 2 3 2546)) (.leaf (.ubHLePi 13 3 2 6356))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 13 4 1 3402)) (.node (.leaf (.ubHGe0 13 5 0 36)) (.leaf (.ubHGe0 13 0 4 746))))
            (.node (.node (.leaf (.ubHGe0 13 1 3 3859)) (.leaf (.ubHGe0 13 2 2 12201))) (.node (.leaf (.ubHGe0 13 3 1 12626)) (.leaf (.ubHGe0 13 4 0 1780)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 13 0 3 2027)) (.leaf (.ubHLePi 13 1 2 10887))) (.node (.leaf (.ubHLePi 13 2 1 19558)) (.leaf (.ubHLePi 13 3 0 6531))))
            (.node (.node (.leaf (.ubHGe0 13 0 2 3849)) (.leaf (.ubHGe0 13 1 1 14205))) (.node (.leaf (.ubHGe0 13 2 0 9431)) (.leaf (.ubHLePi 13 0 1 4067))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 13 1 0 6290)) (.leaf (.ubHGe0 13 0 0 1630))) (.node (.leaf (.ubHLePi 14 0 6 7)) (.leaf (.ubHLePi 14 1 5 90))))
            (.node (.node (.leaf (.ubHLePi 14 2 4 981)) (.leaf (.ubHLePi 14 3 3 4725))) (.node (.leaf (.ubHLePi 14 4 2 8949)) (.leaf (.ubHLePi 14 5 1 6012)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 14 6 0 1953)) (.leaf (.ubHGe0 14 0 5 111))) (.node (.leaf (.ubHGe0 14 1 4 2241)) (.leaf (.ubHGe0 14 2 3 16909))))
            (.node (.node (.leaf (.ubHGe0 14 3 2 46726)) (.leaf (.ubHGe0 14 4 1 44922))) (.node (.leaf (.ubHGe0 14 5 0 16358)) (.leaf (.ubHLePi 14 0 4 1295)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 14 1 3 20050)) (.node (.leaf (.ubHLePi 14 2 2 89581)) (.leaf (.ubHLePi 14 3 1 128315))))
            (.node (.node (.leaf (.ubHLePi 14 4 0 59113)) (.leaf (.ubHGe0 14 0 3 7901))) (.node (.leaf (.ubHGe0 14 1 2 75112)) (.leaf (.ubHGe0 14 2 1 177211)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 14 3 0 114223)) (.leaf (.ubHLePi 14 0 2 23329))) (.node (.leaf (.ubHLePi 14 1 1 119244)) (.leaf (.ubHLePi 14 2 0 122666))))
            (.node (.node (.leaf (.ubHGe0 14 0 1 31445)) (.leaf (.ubHGe0 14 1 0 69062))) (.node (.leaf (.ubHLePi 14 0 0 15912)) (.leaf (.ubHLePi 15 0 6 1))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 15 1 5 69)) (.leaf (.ubHLePi 15 2 4 706))) (.node (.leaf (.ubHLePi 15 3 3 2411)) (.leaf (.ubHLePi 15 4 2 4203))))
            (.node (.node (.leaf (.ubHLePi 15 5 1 4027)) (.leaf (.ubHLePi 15 6 0 1515))) (.node (.leaf (.ubHGe0 15 0 5 69)) (.leaf (.ubHGe0 15 1 4 1597)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 15 2 3 9210)) (.leaf (.ubHGe0 15 3 2 22239))) (.node (.leaf (.ubHGe0 15 4 1 26535)) (.leaf (.ubHGe0 15 5 0 12319))))
            (.node (.node (.leaf (.ubHLePi 15 0 4 891)) (.leaf (.ubHLePi 15 1 3 11436))) (.node (.leaf (.ubHLePi 15 2 2 43814)) (.leaf (.ubHLePi 15 3 1 70298)))))))))
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 15 4 0 41376)) (.node (.leaf (.ubHGe0 15 0 3 4637)) (.leaf (.ubHGe0 15 1 2 37907))))
            (.node (.node (.leaf (.ubHGe0 15 2 1 93223)) (.leaf (.ubHGe0 15 3 0 73937))) (.node (.leaf (.ubHLePi 15 0 2 12129)) (.leaf (.ubHLePi 15 1 1 61627)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 15 2 0 74266)) (.leaf (.ubHGe0 15 0 1 16194))) (.node (.leaf (.ubHGe0 15 1 0 39735)) (.leaf (.ubHLePi 15 0 0 8834))))
            (.node (.node (.leaf (.ubHGe0 16 1 5 8)) (.leaf (.ubHGe0 16 2 4 316))) (.node (.leaf (.ubHGe0 16 3 3 2568)) (.leaf (.ubHGe0 16 4 2 6897))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 16 5 1 7305)) (.leaf (.ubHGe0 16 6 0 4697))) (.node (.leaf (.ubHLePi 16 0 5 8)) (.leaf (.ubHLePi 16 1 4 630))))
            (.node (.node (.leaf (.ubHLePi 16 2 3 8366)) (.leaf (.ubHLePi 16 3 2 33014))) (.node (.leaf (.ubHLePi 16 4 1 47176)) (.leaf (.ubHLePi 16 5 0 32796)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 16 0 4 314)) (.leaf (.ubHGe0 16 1 3 9018))) (.node (.leaf (.ubHGe0 16 2 2 58270)) (.leaf (.ubHGe0 16 3 1 119821))))
            (.node (.node (.leaf (.ubHGe0 16 4 0 98479)) (.leaf (.ubHLePi 16 0 3 3221))) (.node (.leaf (.ubHLePi 16 1 2 45086)) (.leaf (.ubHLePi 16 2 1 149732)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 16 3 0 160808)) (.node (.leaf (.ubHGe0 16 0 2 12933)) (.leaf (.ubHGe0 16 1 1 92184))))
            (.node (.node (.leaf (.ubHGe0 16 2 0 149154)) (.leaf (.ubHLePi 16 0 1 22402))) (.node (.leaf (.ubHLePi 16 1 0 73996)) (.leaf (.ubHGe0 16 0 0 15271)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 17 3 3 91)) (.leaf (.ubHGe0 17 4 2 199))) (.node (.leaf (.ubHGe0 17 5 1 1847)) (.leaf (.ubHGe0 17 6 0 7769))))
            (.node (.node (.leaf (.ubHLePi 17 2 3 238)) (.leaf (.ubHLePi 17 3 2 914))) (.node (.leaf (.ubHLePi 17 4 1 8720)) (.leaf (.ubHLePi 17 5 0 44573))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 17 1 3 209)) (.leaf (.ubHGe0 17 2 2 1508))) (.node (.leaf (.ubHGe0 17 3 1 16741)) (.leaf (.ubHGe0 17 4 0 107129))))
            (.node (.node (.leaf (.ubHLePi 17 0 3 62)) (.leaf (.ubHLePi 17 1 2 1075))) (.node (.leaf (.ubHLePi 17 2 1 16286)) (.leaf (.ubHLePi 17 3 0 138017)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 17 0 2 283)) (.leaf (.ubHGe0 17 1 1 8008))) (.node (.leaf (.ubHGe0 17 2 0 100493)) (.leaf (.ubHLePi 17 0 1 1589))))
            (.node (.node (.leaf (.ubHLePi 17 1 0 39197)) (.leaf (.ubHGe0 17 0 0 6397))) (.node (.leaf (.ubHGe0 18 3 3 410)) (.leaf (.ubHGe0 18 4 2 3807))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHGe0 18 5 1 7532)) (.node (.leaf (.ubHLePi 18 6 0 2298)) (.leaf (.ubHLePi 18 2 3 1160))))
            (.node (.node (.leaf (.ubHLePi 18 3 2 15547)) (.leaf (.ubHLePi 18 4 1 42845))) (.node (.leaf (.ubHGe0 18 5 0 5284)) (.leaf (.ubHGe0 18 1 3 1097)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 18 2 2 23724)) (.leaf (.ubHGe0 18 3 1 95995))) (.node (.leaf (.ubHGe0 18 4 0 9132)) (.leaf (.ubHLePi 18 0 3 347))))
            (.node (.node (.leaf (.ubHLePi 18 1 2 16047)) (.leaf (.ubHLePi 18 2 1 106239))) (.node (.leaf (.ubHLePi 18 3 0 43495)) (.leaf (.ubHGe0 18 0 2 4062))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 18 1 1 58214)) (.leaf (.ubHGe0 18 2 0 57324))) (.node (.leaf (.ubHLePi 18 0 1 12657)) (.leaf (.ubHLePi 18 1 0 33319))))
            (.node (.node (.leaf (.ubHGe0 18 0 0 7373)) (.leaf (.ubHGe0 19 4 2 374))) (.node (.leaf (.ubHGe0 19 5 1 3151)) (.leaf (.ubHGe0 19 6 0 16506)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 19 3 2 1465)) (.leaf (.ubHLePi 19 4 1 15674))) (.node (.leaf (.ubHLePi 19 5 0 94930)) (.leaf (.ubHGe0 19 2 2 2139))))
            (.node (.node (.leaf (.ubHGe0 19 3 1 31236)) (.leaf (.ubHGe0 19 4 0 228983))) (.node (.leaf (.ubHLePi 19 1 2 1385)) (.leaf (.ubHLePi 19 2 1 31160)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 19 3 0 296290)) (.node (.leaf (.ubHGe0 19 0 2 336)) (.leaf (.ubHGe0 19 1 1 15556))))
            (.node (.node (.leaf (.ubHGe0 19 2 0 216757)) (.leaf (.ubHLePi 19 0 1 3108))) (.node (.leaf (.ubHLePi 19 1 0 84955)) (.leaf (.ubHGe0 20 5 1 8727)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 20 6 0 34591)) (.leaf (.ubHLePi 20 4 1 40501))) (.node (.leaf (.ubHLePi 20 5 0 201852)) (.leaf (.ubHGe0 20 3 1 75616))))
            (.node (.node (.leaf (.ubHGe0 20 4 0 492052)) (.leaf (.ubHLePi 20 2 1 70929))) (.node (.leaf (.ubHLePi 20 3 0 641163)) (.leaf (.ubHGe0 20 1 1 33404))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 20 2 0 470875)) (.leaf (.ubHLePi 20 0 1 6316))) (.node (.leaf (.ubHLePi 20 1 0 184755)) (.leaf (.ubHGe0 20 0 0 30251))))
            (.node (.node (.leaf (.ubHLePi 21 6 0 16609)) (.leaf (.ubHGe0 21 5 0 91923))) (.node (.leaf (.ubHLePi 21 4 0 213246)) (.leaf (.ubHGe0 21 3 0 265192)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 21 2 0 186338)) (.leaf (.ubHGe0 21 1 0 70104))) (.node (.leaf (.ubHLePi 21 0 0 11027)) (.leaf (.ubPHi 6 113439))))
            (.node (.node (.leaf (.ubPHi 5 1447889)) (.leaf (.ubPHi 4 1391385))) (.node (.leaf (.ubPHi 3 4205573)) (.leaf (.ubPHi 2 1193963))))))))))))

lemma step1bScale_pos : 0 < step1bScale := by decide
lemma step1bLb_strict : 20 * (step1bScale : ℤ) < 21 * step1bLb := by decide
lemma step1bCert_u_ok :
    checkBinoBoundU 21 6 [] step1bCert 20 1 step1bScale step1bLb = true := by
  decide
private lemma step1bCert_c_0 : checkBinoCForJ 21 6 0 step1bCert = true := by decide
private lemma step1bCert_c_1 : checkBinoCForJ 21 6 1 step1bCert = true := by decide
private lemma step1bCert_c_2 : checkBinoCForJ 21 6 2 step1bCert = true := by decide
private lemma step1bCert_c_3 : checkBinoCForJ 21 6 3 step1bCert = true := by decide
private lemma step1bCert_c_4 : checkBinoCForJ 21 6 4 step1bCert = true := by decide
private lemma step1bCert_c_5 : checkBinoCForJ 21 6 5 step1bCert = true := by decide
private lemma step1bCert_c_6 : checkBinoCForJ 21 6 6 step1bCert = true := by decide
private lemma step1bCert_c_7 : checkBinoCForJ 21 6 7 step1bCert = true := by decide
private lemma step1bCert_c_8 : checkBinoCForJ 21 6 8 step1bCert = true := by decide
private lemma step1bCert_c_9 : checkBinoCForJ 21 6 9 step1bCert = true := by decide
private lemma step1bCert_c_10 : checkBinoCForJ 21 6 10 step1bCert = true := by decide
private lemma step1bCert_c_11 : checkBinoCForJ 21 6 11 step1bCert = true := by decide
private lemma step1bCert_c_12 : checkBinoCForJ 21 6 12 step1bCert = true := by decide
private lemma step1bCert_c_13 : checkBinoCForJ 21 6 13 step1bCert = true := by decide
private lemma step1bCert_c_14 : checkBinoCForJ 21 6 14 step1bCert = true := by decide
private lemma step1bCert_c_15 : checkBinoCForJ 21 6 15 step1bCert = true := by decide
private lemma step1bCert_c_16 : checkBinoCForJ 21 6 16 step1bCert = true := by decide
private lemma step1bCert_c_17 : checkBinoCForJ 21 6 17 step1bCert = true := by decide
private lemma step1bCert_c_18 : checkBinoCForJ 21 6 18 step1bCert = true := by decide
private lemma step1bCert_c_19 : checkBinoCForJ 21 6 19 step1bCert = true := by decide
private lemma step1bCert_c_20 : checkBinoCForJ 21 6 20 step1bCert = true := by decide
private lemma step1bCert_c_21 : checkBinoCForJ 21 6 21 step1bCert = true := by decide
lemma step1bCert_c_ok : ∀ j ≤ 21, checkBinoCForJ 21 6 j step1bCert = true := by
  intro j hj
  match j with
  | 0 => exact step1bCert_c_0
  | 1 => exact step1bCert_c_1
  | 2 => exact step1bCert_c_2
  | 3 => exact step1bCert_c_3
  | 4 => exact step1bCert_c_4
  | 5 => exact step1bCert_c_5
  | 6 => exact step1bCert_c_6
  | 7 => exact step1bCert_c_7
  | 8 => exact step1bCert_c_8
  | 9 => exact step1bCert_c_9
  | 10 => exact step1bCert_c_10
  | 11 => exact step1bCert_c_11
  | 12 => exact step1bCert_c_12
  | 13 => exact step1bCert_c_13
  | 14 => exact step1bCert_c_14
  | 15 => exact step1bCert_c_15
  | 16 => exact step1bCert_c_16
  | 17 => exact step1bCert_c_17
  | 18 => exact step1bCert_c_18
  | 19 => exact step1bCert_c_19
  | 20 => exact step1bCert_c_20
  | 21 => exact step1bCert_c_21
  | _ + 22 => omega

def step1cScale : ℕ := 1000000
def step1cLb : ℤ := (-876243)
def step1cCert : BinTree BinoStep :=
  (.node
    (.node
      (.node
        (.node (.leaf (.eqP0 (-11250678))) (.node (.leaf (.eqP1 21016024)) (.leaf (.eqB00 0 3684163))))
        (.node (.leaf (.ubPHi 11 1654018)) (.node (.leaf (.ubPLo 16 1781250)) (.leaf (.ubHLePj 0 0 1 13508272)))))
      (.node
        (.node (.leaf (.ubHMcc 0 0 2 17361111)) (.node (.leaf (.ubHLePj 0 0 3 9071181)) (.leaf (.ubHGe0 0 0 5 5566406))))
        (.node (.node (.leaf (.ubHLePi 0 0 6 4750000)) (.leaf (.ubHMcc 0 0 11 1032851))) (.node (.leaf (.ubHLePj 0 0 18 1219655)) (.leaf (.ubHMcc 0 0 20 1736111))))))
    (.node
      (.node
        (.node (.leaf (.ubHLePj 0 0 21 831535)) (.node (.leaf (.ubHGe0 0 0 6 1138)) (.leaf (.ubHLePi 0 0 5 5585))))
        (.node (.leaf (.ubHGe0 0 0 4 11475)) (.node (.leaf (.ubHLePi 0 0 3 12614)) (.leaf (.ubHGe0 0 0 2 7814)))))
      (.node
        (.node (.leaf (.ubHLePi 0 0 1 2582)) (.node (.leaf (.ubHGe0 0 0 0 355)) (.leaf (.ubPHi 6 4162))))
        (.node (.node (.leaf (.ubPLo 5 17809)) (.leaf (.ubPHi 4 54975))) (.node (.leaf (.ubPLo 3 56511)) (.leaf (.ubPHi 2 49039)))))))

lemma step1cScale_pos : 0 < step1cScale := by decide
lemma step1cLb_strict : (-1) * (step1cScale : ℤ) < 1 * step1cLb := by decide
lemma step1cCert_u_ok :
    checkBinoBoundU 21 6 [] step1cCert 21 (-1) step1cScale step1cLb = true := by
  decide
private lemma step1cCert_c_0 : checkBinoCForJ 21 6 0 step1cCert = true := by decide
private lemma step1cCert_c_rest :
    ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21] : List ℕ).all (fun j => checkBinoCForJ 21 6 j step1cCert) = true := by
  decide
lemma step1cCert_c_ok : ∀ j ≤ 21, checkBinoCForJ 21 6 j step1cCert = true := by
  have hcov : ∀ j : Fin 22, j.val = 0 ∨ j.val ∈ ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21] : List ℕ) := by decide
  intro j hj
  rcases hcov ⟨j, by omega⟩ with h | h
  · dsimp only at h; rw [h]; exact step1cCert_c_0
  · exact List.all_eq_true.mp step1cCert_c_rest j h

def step2aScale : ℕ := 5000000000
def step2aLb : ℤ := 4977194886
def step2aCert : BinTree BinoStep :=
  (.node
    (.node
      (.node
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.eqP1 (-397151485949))) (.node (.leaf (.eqB00 0 130959510555)) (.leaf (.eqDiag 1 3950451150))))
            (.node (.node (.leaf (.eqB00 2 (-135882295783))) (.leaf (.eqB10 2 62658887049))) (.node (.leaf (.eqB01 2 338839859551)) (.leaf (.eqDiag 3 3049972507)))))
            (.node
            (.node (.node (.leaf (.eqB00 4 (-19772560737))) (.leaf (.eqB10 4 17312951601))) (.node (.leaf (.eqB01 4 40114991491)) (.leaf (.eqDiag 5 94603874))))
            (.node (.node (.leaf (.eqB00 5 (-3053491367))) (.leaf (.eqB01 5 10562314173))) (.node (.leaf (.eqDiag 7 3190361527)) (.leaf (.eqB00 7 (-7858510682)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqB10 7 9673591374)) (.leaf (.eqB01 7 12993427212))) (.node (.leaf (.eqDiag 9 4967809718)) (.leaf (.eqB00 9 (-11800498090)))))
            (.node (.node (.leaf (.eqB10 9 8239855976)) (.leaf (.eqB01 9 22759470016))) (.node (.leaf (.eqB00 10 (-8254123205))) (.leaf (.eqB10 10 10175197555)))))
            (.node
            (.node (.node (.leaf (.eqB01 10 11841302735)) (.leaf (.eqDiag 11 1551090582))) (.node (.leaf (.eqB00 11 (-2610528336))) (.leaf (.eqB10 11 3541888023))))
            (.node (.node (.leaf (.eqB01 11 560575261)) (.leaf (.eqB00 13 (-5628734766)))) (.node (.leaf (.eqB10 13 14159653957)) (.leaf (.eqB01 13 6917031140)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.eqDiag 14 552143849)) (.node (.leaf (.eqB10 14 3008227973)) (.leaf (.eqDiag 16 405053541))))
            (.node (.node (.leaf (.eqB00 16 (-5336885203))) (.leaf (.eqB10 16 8128626815))) (.node (.leaf (.eqB01 16 8366488614)) (.leaf (.eqDiag 17 1314792906)))))
            (.node
            (.node (.node (.leaf (.eqB00 17 (-6115688391))) (.leaf (.eqB10 17 1082668617))) (.node (.leaf (.eqB01 17 24599933549)) (.leaf (.eqDiag 19 894124943))))
            (.node (.node (.leaf (.eqB00 19 (-39310328))) (.leaf (.eqB10 20 39587381231))) (.node (.leaf (.eqB01 20 13642720656)) (.leaf (.eqDiag 21 631881569))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqB00 21 (-7033189885))) (.leaf (.eqB10 21 4866782081))) (.node (.leaf (.eqSym 0 5 0 (-2053447596))) (.leaf (.eqSym 0 9 0 2419887740))))
            (.node (.node (.leaf (.eqSym 0 15 0 (-3650573504))) (.leaf (.eqSym 0 19 0 14410158570))) (.node (.leaf (.eqSym 0 20 0 (-17606593744))) (.leaf (.eqSym 0 21 0 5704021101)))))
            (.node
            (.node (.node (.leaf (.eqSym 1 2 1 14863543421)) (.leaf (.eqSym 1 3 1 (-16352630032)))) (.node (.leaf (.eqSym 1 5 1 6949867763)) (.leaf (.eqSym 1 9 1 (-2707740687)))))
            (.node (.node (.leaf (.eqSym 1 11 1 1235532047)) (.leaf (.eqSym 1 20 1 (-111277865)))) (.node (.leaf (.eqSym 1 21 1 73156503)) (.leaf (.eqSym 2 3 1 43045614844))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 2 3 2 (-7850073687))) (.node (.leaf (.eqSym 2 4 1 (-54687089979))) (.leaf (.eqSym 2 4 2 5674981448))))
            (.node (.node (.leaf (.eqSym 2 5 2 3551968186)) (.leaf (.eqSym 2 6 0 21780410925))) (.node (.leaf (.eqSym 2 6 1 24347092331)) (.leaf (.eqSym 2 6 2 (-1520688159))))))
            (.node
            (.node (.node (.leaf (.eqSym 2 7 1 (-14639348898))) (.leaf (.eqSym 2 9 0 (-30471493414)))) (.node (.leaf (.eqSym 2 11 1 11949230640)) (.leaf (.eqSym 2 11 2 (-4657918196)))))
            (.node (.node (.leaf (.eqSym 2 12 1 25999285039)) (.leaf (.eqSym 2 13 1 (-26827226388)))) (.node (.leaf (.eqSym 2 14 0 30031065637)) (.leaf (.eqSym 2 15 1 3623103455))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 2 16 1 (-69510991148))) (.leaf (.eqSym 2 17 0 (-23675470783)))) (.node (.leaf (.eqSym 2 17 1 (-24062842110))) (.leaf (.eqSym 2 17 2 8899740260))))
            (.node (.node (.leaf (.eqSym 2 19 0 6048760583)) (.leaf (.eqSym 2 19 1 64089326884))) (.node (.leaf (.eqSym 2 19 2 8646482894)) (.leaf (.eqSym 2 20 1 (-37280789987))))))
            (.node
            (.node (.node (.leaf (.eqSym 2 21 2 (-6185058742))) (.leaf (.eqSym 3 4 0 (-27262300099)))) (.node (.leaf (.eqSym 3 4 1 43536780079)) (.leaf (.eqSym 3 5 0 (-5847314070)))))
            (.node (.node (.leaf (.eqSym 3 5 1 (-15252565046))) (.leaf (.eqSym 3 5 2 (-15779150535)))) (.node (.leaf (.eqSym 3 5 3 745888725)) (.leaf (.eqSym 3 8 1 36185127341)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 3 8 2 (-16676546424))) (.node (.leaf (.eqSym 3 8 3 23391119233)) (.leaf (.eqSym 3 9 0 23189937765))))
            (.node (.node (.leaf (.eqSym 3 9 1 (-12857984755))) (.leaf (.eqSym 3 9 2 21740903128))) (.node (.leaf (.eqSym 3 10 0 (-6407793900))) (.leaf (.eqSym 3 10 1 (-3037586984))))))
            (.node
            (.node (.node (.leaf (.eqSym 3 10 3 (-32964775927))) (.leaf (.eqSym 3 11 0 12753628301))) (.node (.leaf (.eqSym 3 11 1 (-50803586455))) (.leaf (.eqSym 3 11 2 10263848456))))
            (.node (.node (.leaf (.eqSym 3 12 3 9766759614)) (.leaf (.eqSym 3 13 1 16652730184))) (.node (.leaf (.eqSym 3 14 0 (-21746490782))) (.leaf (.eqSym 3 15 1 2371608054))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 3 17 0 6242836428)) (.leaf (.eqSym 3 17 1 25132996025))) (.node (.leaf (.eqSym 3 17 2 (-6718708533))) (.leaf (.eqSym 3 18 0 643302179))))
            (.node (.node (.leaf (.eqSym 3 18 1 2553937147)) (.leaf (.eqSym 3 18 2 11309505155))) (.node (.leaf (.eqSym 3 19 1 (-17788470778))) (.leaf (.eqSym 3 19 2 (-38482966480))))))
            (.node
            (.node (.node (.leaf (.eqSym 3 19 3 14091176379)) (.leaf (.eqSym 3 20 2 26493041546))) (.node (.leaf (.eqSym 3 20 3 (-40793233908))) (.leaf (.eqSym 3 21 3 2609723062))))
            (.node (.node (.leaf (.eqSym 4 5 2 20683264624)) (.leaf (.eqSym 4 7 0 (-6520036295)))) (.node (.leaf (.eqSym 4 7 4 (-3820008174))) (.leaf (.eqSym 4 8 4 (-12050398918))))))))))
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 4 9 1 12370814749)) (.node (.leaf (.eqSym 4 9 2 (-48702661159))) (.leaf (.eqSym 4 10 0 (-3590691890)))))
            (.node (.node (.leaf (.eqSym 4 10 4 24196139857)) (.leaf (.eqSym 4 11 2 38832114296))) (.node (.leaf (.eqSym 4 13 1 (-8187680237))) (.leaf (.eqSym 4 13 4 (-11291782764))))))
            (.node
            (.node (.node (.leaf (.eqSym 4 14 0 3655269785)) (.leaf (.eqSym 4 14 4 (-1468268164)))) (.node (.leaf (.eqSym 4 15 0 1701763390)) (.leaf (.eqSym 4 17 0 (-2166174334)))))
            (.node (.node (.leaf (.eqSym 4 17 1 1979507190)) (.leaf (.eqSym 4 17 2 (-6059051990)))) (.node (.leaf (.eqSym 4 18 2 (-4603218918))) (.leaf (.eqSym 4 19 2 5524534595))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 4 19 4 (-1884925861))) (.leaf (.eqSym 4 20 4 10153172676))) (.node (.leaf (.eqSym 5 6 1 (-23911824528))) (.leaf (.eqSym 5 6 3 3880336023))))
            (.node (.node (.leaf (.eqSym 5 6 5 2665671535)) (.leaf (.eqSym 5 8 0 6898778682))) (.node (.leaf (.eqSym 5 8 1 12282364342)) (.leaf (.eqSym 5 8 3 2208511804)))))
            (.node
            (.node (.node (.leaf (.eqSym 5 8 4 2851835736)) (.leaf (.eqSym 5 8 5 (-10048359622)))) (.node (.leaf (.eqSym 5 9 0 (-6857803632))) (.leaf (.eqSym 5 9 2 18820406639))))
            (.node (.node (.leaf (.eqSym 5 9 5 (-4693408336))) (.leaf (.eqSym 5 10 4 1891415605))) (.node (.leaf (.eqSym 5 10 5 24819294713)) (.leaf (.eqSym 5 11 0 (-5987048432))))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 5 11 1 (-1718101525))) (.node (.leaf (.eqSym 5 11 2 (-8033916890))) (.leaf (.eqSym 5 11 4 (-19761341868)))))
            (.node (.node (.leaf (.eqSym 5 11 5 (-10738898999))) (.leaf (.eqSym 5 12 0 6195828815))) (.node (.leaf (.eqSym 5 12 1 (-7377775092))) (.leaf (.eqSym 5 12 3 (-8971968366))))))
            (.node
            (.node (.node (.leaf (.eqSym 5 13 1 11567808136)) (.leaf (.eqSym 5 13 4 16174406156))) (.node (.leaf (.eqSym 5 15 1 (-2922725496))) (.leaf (.eqSym 5 15 2 (-1145434612)))))
            (.node (.node (.leaf (.eqSym 5 16 1 234562849)) (.leaf (.eqSym 5 16 4 4217121487))) (.node (.leaf (.eqSym 5 16 5 (-4647482960))) (.leaf (.eqSym 5 17 5 308375971))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 5 18 2 (-1184972862))) (.leaf (.eqSym 5 19 3 3211590153))) (.node (.leaf (.eqSym 5 19 4 (-5373437117))) (.leaf (.eqSym 5 19 5 2429411573))))
            (.node (.node (.leaf (.eqSym 6 7 3 3197998442)) (.leaf (.eqSym 6 7 5 8421864203))) (.node (.leaf (.eqSym 6 8 1 (-22496320494))) (.leaf (.eqSym 6 8 3 (-199175367))))))
            (.node
            (.node (.node (.leaf (.eqSym 6 8 5 7086707053)) (.leaf (.eqSym 6 9 0 3699506669))) (.node (.leaf (.eqSym 6 9 5 (-17594785118))) (.leaf (.eqSym 6 9 6 (-1428542760)))))
            (.node (.node (.leaf (.eqSym 6 11 1 15603319066)) (.leaf (.eqSym 6 11 2 (-4186480570)))) (.node (.leaf (.eqSym 6 11 5 3761718892)) (.leaf (.eqSym 6 12 0 (-2732015780)))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 6 12 1 3749561488)) (.node (.leaf (.eqSym 6 12 3 8929246296)) (.leaf (.eqSym 6 13 0 (-2453334190)))))
            (.node (.node (.leaf (.eqSym 6 13 1 (-8531083432))) (.leaf (.eqSym 6 13 4 948136033))) (.node (.leaf (.eqSym 6 13 6 2340441319)) (.leaf (.eqSym 6 14 0 2945017268)))))
            (.node
            (.node (.node (.leaf (.eqSym 6 14 2 2665792411)) (.leaf (.eqSym 6 14 3 (-13934164160)))) (.node (.leaf (.eqSym 6 15 1 (-85283617))) (.leaf (.eqSym 6 15 3 61368094))))
            (.node (.node (.leaf (.eqSym 6 16 1 (-350788737))) (.leaf (.eqSym 6 16 3 5825062719))) (.node (.leaf (.eqSym 6 19 4 (-948136033))) (.leaf (.eqSym 6 19 5 2871993541))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 6 19 6 (-3973880879))) (.leaf (.eqSym 6 20 6 2798838290))) (.node (.leaf (.eqSym 7 8 1 6047606270)) (.leaf (.eqSym 7 8 2 (-36673081893)))))
            (.node (.node (.leaf (.eqSym 7 8 7 10869216592)) (.leaf (.eqSym 7 9 0 (-7754895555)))) (.node (.leaf (.eqSym 7 9 4 31490536672)) (.leaf (.eqSym 7 9 6 17208449852)))))
            (.node
            (.node (.node (.leaf (.eqSym 7 9 7 (-230038314))) (.leaf (.eqSym 7 10 0 (-3052284151)))) (.node (.leaf (.eqSym 7 10 2 18358439209)) (.leaf (.eqSym 7 10 3 40744697406))))
            (.node (.node (.leaf (.eqSym 7 10 4 (-44676862671))) (.leaf (.eqSym 7 10 6 (-15147400663)))) (.node (.leaf (.eqSym 7 10 7 (-30041118415))) (.leaf (.eqSym 7 11 0 9472865945)))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 7 11 7 24473049241)) (.leaf (.eqSym 7 12 6 5049699250))) (.node (.leaf (.eqSym 7 13 1 (-4882647369))) (.leaf (.eqSym 7 13 3 (-30594785306)))))
            (.node (.node (.leaf (.eqSym 7 14 0 (-922931847))) (.leaf (.eqSym 7 14 3 13337015606))) (.node (.leaf (.eqSym 7 14 7 (-4145268388))) (.leaf (.eqSym 7 15 1 (-25835531))))))
            (.node
            (.node (.node (.leaf (.eqSym 7 15 7 1243962203)) (.leaf (.eqSym 7 16 3 5867233773))) (.node (.leaf (.eqSym 7 17 3 4368241438)) (.leaf (.eqSym 7 17 4 (-21158086648)))))
            (.node (.node (.leaf (.eqSym 7 17 5 28640956991)) (.leaf (.eqSym 7 17 6 (-2799681724)))) (.node (.leaf (.eqSym 7 17 7 (-4727388215))) (.leaf (.eqSym 7 18 5 (-1904450104)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 7 18 6 (-14994753740))) (.leaf (.eqSym 7 18 7 8958887473))) (.node (.leaf (.eqSym 7 19 6 4578806131)) (.leaf (.eqSym 7 19 7 (-2338814808)))))
            (.node (.node (.leaf (.eqSym 8 9 2 1725276203)) (.leaf (.eqSym 8 9 4 (-18922125140)))) (.node (.leaf (.eqSym 8 9 6 17178994904)) (.leaf (.eqSym 8 10 0 17042894783)))))
            (.node
            (.node (.node (.leaf (.eqSym 8 10 2 (-27451075172))) (.leaf (.eqSym 8 10 8 942866890))) (.node (.leaf (.eqSym 8 11 0 (-15502277397))) (.leaf (.eqSym 8 11 3 (-31132338871)))))
            (.node (.node (.leaf (.eqSym 8 11 4 33442431832)) (.leaf (.eqSym 8 11 7 6980827927))) (.node (.leaf (.eqSym 8 11 8 (-7167811335))) (.leaf (.eqSym 8 12 1 (-4274705230)))))))))))
      (.node
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 8 12 3 (-4367878802))) (.node (.leaf (.eqSym 8 12 6 (-36074768491))) (.leaf (.eqSym 8 13 1 12081632936))))
            (.node (.node (.leaf (.eqSym 8 13 3 32337562831)) (.leaf (.eqSym 8 13 4 6892959535))) (.node (.leaf (.eqSym 8 14 2 (-6350125758))) (.leaf (.eqSym 8 14 7 18157017156)))))
            (.node
            (.node (.node (.leaf (.eqSym 8 16 4 (-12388312101))) (.leaf (.eqSym 8 16 5 (-3556169749)))) (.node (.leaf (.eqSym 8 16 8 128390161)) (.leaf (.eqSym 8 19 6 12200883844))))
            (.node (.node (.leaf (.eqSym 8 19 7 881348725)) (.leaf (.eqSym 8 19 8 (-10924422707)))) (.node (.leaf (.eqSym 8 20 7 (-11239394908))) (.leaf (.eqSym 8 20 8 11079213514))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 9 10 0 (-9284772841))) (.leaf (.eqSym 9 10 1 1149617648))) (.node (.leaf (.eqSym 9 10 7 29411236891)) (.leaf (.eqSym 9 10 9 14008093753))))
            (.node (.node (.leaf (.eqSym 9 11 0 5303276486)) (.leaf (.eqSym 9 11 1 (-774607290)))) (.node (.leaf (.eqSym 9 11 8 (-7417469000))) (.leaf (.eqSym 9 11 9 (-8157474551))))))
            (.node
            (.node (.node (.leaf (.eqSym 9 12 1 2885642188)) (.leaf (.eqSym 9 12 6 14052609957))) (.node (.leaf (.eqSym 9 12 9 (-1912729028))) (.leaf (.eqSym 9 13 1 (-2612742896)))))
            (.node (.node (.leaf (.eqSym 9 13 4 (-5415175850))) (.leaf (.eqSym 9 14 7 (-22902079424)))) (.node (.leaf (.eqSym 9 15 5 5148539947)) (.leaf (.eqSym 9 16 8 5873108569)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 9 18 7 15495174161)) (.node (.leaf (.eqSym 9 18 8 (-4340879019))) (.leaf (.eqSym 9 18 9 (-2610214622)))))
            (.node (.node (.leaf (.eqSym 9 19 7 (-16313783482))) (.leaf (.eqSym 9 19 8 (-13439804581)))) (.node (.leaf (.eqSym 9 19 9 19931247315)) (.leaf (.eqSym 9 20 8 18995506654)))))
            (.node
            (.node (.node (.leaf (.eqSym 9 20 9 (-16450280579))) (.leaf (.eqSym 10 11 0 208807770))) (.node (.leaf (.eqSym 10 11 2 6530538713)) (.leaf (.eqSym 10 11 7 (-15140744932)))))
            (.node (.node (.leaf (.eqSym 10 11 9 3682684432)) (.leaf (.eqSym 10 11 10 547450951))) (.node (.leaf (.eqSym 10 12 1 (-681793071))) (.leaf (.eqSym 10 12 3 2063233973))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 10 12 6 (-19673998894))) (.leaf (.eqSym 10 12 7 34898741525))) (.node (.leaf (.eqSym 10 13 3 (-9231658219))) (.leaf (.eqSym 10 13 8 (-22302616621)))))
            (.node (.node (.leaf (.eqSym 10 13 9 13616327209)) (.leaf (.eqSym 10 14 7 30010778794))) (.node (.leaf (.eqSym 10 15 7 (-14710448715))) (.leaf (.eqSym 10 15 8 (-918810161))))))
            (.node
            (.node (.node (.leaf (.eqSym 10 16 6 7452008940)) (.leaf (.eqSym 10 16 8 (-53933492)))) (.node (.leaf (.eqSym 10 16 10 2772989071)) (.leaf (.eqSym 10 17 8 (-29172172194)))))
            (.node (.node (.leaf (.eqSym 10 17 9 20947958806)) (.leaf (.eqSym 10 17 10 (-16580210183)))) (.node (.leaf (.eqSym 10 18 7 995910040)) (.leaf (.eqSym 10 18 10 1611119987))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 10 19 8 8347624343)) (.node (.leaf (.eqSym 10 19 9 9748007615)) (.leaf (.eqSym 10 20 9 (-11863249632)))))
            (.node (.node (.leaf (.eqSym 10 20 10 3950369159)) (.leaf (.eqSym 11 12 3 (-315876989)))) (.node (.leaf (.eqSym 11 12 4 793099686)) (.leaf (.eqSym 11 12 6 7798850898)))))
            (.node
            (.node (.node (.leaf (.eqSym 11 12 9 4769161399)) (.leaf (.eqSym 11 12 11 828896226))) (.node (.leaf (.eqSym 11 13 4 (-4080999816))) (.leaf (.eqSym 11 13 10 (-8783768675)))))
            (.node (.node (.leaf (.eqSym 11 14 4 5676406939)) (.leaf (.eqSym 11 14 7 (-16443780532)))) (.node (.leaf (.eqSym 11 14 9 (-7526318525))) (.leaf (.eqSym 11 14 11 639326482))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 11 15 5 301527235)) (.leaf (.eqSym 11 15 8 11513912071))) (.node (.leaf (.eqSym 11 15 11 (-1484965228))) (.leaf (.eqSym 11 16 6 (-2119022908)))))
            (.node (.node (.leaf (.eqSym 11 16 8 (-3095299572))) (.leaf (.eqSym 11 16 10 (-7142556493)))) (.node (.leaf (.eqSym 11 17 7 (-2268626329))) (.leaf (.eqSym 11 17 8 15694467589)))))
            (.node
            (.node (.node (.leaf (.eqSym 11 17 10 (-5717289886))) (.leaf (.eqSym 11 17 11 21660957184))) (.node (.leaf (.eqSym 11 18 9 (-13954075760))) (.leaf (.eqSym 11 18 10 18345181244))))
            (.node (.node (.leaf (.eqSym 11 18 11 (-11569439897))) (.leaf (.eqSym 11 19 9 (-3097092798)))) (.node (.leaf (.eqSym 11 19 10 3703448175)) (.leaf (.eqSym 11 19 11 (-10467441933))))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 11 20 10 502772346)) (.node (.leaf (.eqSym 11 20 11 1902028526)) (.leaf (.eqSym 11 21 11 115429273))))
            (.node (.node (.leaf (.eqSym 12 13 4 901767687)) (.leaf (.eqSym 12 13 9 16376925901))) (.node (.leaf (.eqSym 12 13 10 524752691)) (.leaf (.eqSym 12 13 12 410235427)))))
            (.node
            (.node (.node (.leaf (.eqSym 12 15 7 (-1193304369))) (.leaf (.eqSym 12 16 8 2479822832))) (.node (.leaf (.eqSym 12 17 11 (-5480845670))) (.leaf (.eqSym 12 18 9 (-305653945)))))
            (.node (.node (.leaf (.eqSym 12 18 11 990651127)) (.leaf (.eqSym 12 19 11 (-466471653)))) (.node (.leaf (.eqSym 12 20 11 (-802495942))) (.leaf (.eqSym 13 14 6 (-7376648599)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 13 14 7 1458020691)) (.leaf (.eqSym 13 15 7 2044971073))) (.node (.leaf (.eqSym 13 15 10 5322731260)) (.leaf (.eqSym 13 16 8 3422253149))))
            (.node (.node (.leaf (.eqSym 13 16 9 (-3331405301))) (.leaf (.eqSym 13 16 13 (-841359103)))) (.node (.leaf (.eqSym 13 17 12 2684748840)) (.leaf (.eqSym 13 18 12 (-2554713276))))))
            (.node
            (.node (.node (.leaf (.eqSym 13 19 12 (-1034360793))) (.leaf (.eqSym 13 19 13 748948112))) (.node (.leaf (.eqSym 13 20 12 420121517)) (.leaf (.eqSym 14 15 8 (-4056880205)))))
            (.node (.node (.leaf (.eqSym 14 15 11 (-3020539573))) (.leaf (.eqSym 14 15 13 (-397332312)))) (.node (.leaf (.eqSym 14 15 14 2002759288)) (.leaf (.eqSym 14 17 14 (-5669876148))))))))))
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 14 18 14 6234836843)) (.node (.leaf (.eqSym 14 20 13 2095366680)) (.leaf (.eqSym 14 20 14 (-1947087800)))))
            (.node (.node (.leaf (.eqSym 14 21 14 (-661659982))) (.leaf (.eqSym 15 16 10 (-2257586250)))) (.node (.leaf (.eqSym 15 16 12 3424035897)) (.leaf (.eqSym 15 16 13 143822647)))))
            (.node
            (.node (.node (.leaf (.eqSym 15 16 14 1452797893)) (.leaf (.eqSym 15 16 15 (-777962273)))) (.node (.leaf (.eqSym 15 17 14 (-3239193682))) (.leaf (.eqSym 15 18 14 503541944))))
            (.node (.node (.leaf (.eqSym 15 18 15 1116959560)) (.leaf (.eqSym 15 19 14 (-613188101)))) (.node (.leaf (.eqSym 15 20 14 89390)) (.leaf (.eqSym 15 20 15 (-665399886)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 15 21 15 501719946)) (.leaf (.eqSym 16 19 14 (-1461838517)))) (.node (.leaf (.eqSym 16 19 15 1802578281)) (.leaf (.eqSym 16 19 16 1001273350))))
            (.node (.node (.leaf (.eqSym 16 20 15 820469939)) (.leaf (.eqSym 16 20 16 (-1857660533)))) (.node (.leaf (.eqSym 17 18 15 1236691628)) (.leaf (.eqSym 17 18 16 (-10098912610))))))
            (.node
            (.node (.node (.leaf (.eqSym 17 18 17 214079590)) (.leaf (.eqSym 17 19 15 822076578))) (.node (.leaf (.eqSym 17 19 16 1522032931)) (.leaf (.eqSym 17 19 17 4966170660))))
            (.node (.node (.leaf (.eqSym 18 19 17 (-6422113738))) (.leaf (.eqSym 18 19 18 (-5162063516)))) (.node (.leaf (.eqSym 18 20 17 823998346)) (.leaf (.eqSym 18 20 18 5246171892)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 18 21 18 (-675412935))) (.node (.leaf (.eqSym 19 20 18 (-2829473122))) (.leaf (.eqSym 19 20 19 (-2083491103)))))
            (.node (.node (.leaf (.eqSym 19 21 19 2095512032)) (.leaf (.eqSym 20 21 20 (-2042904022)))) (.node (.leaf (.eqPFix 2 1 700454974451)) (.leaf (.eqPFix 20 1 43314882262)))))
            (.node
            (.node (.node (.leaf (.eqPFix 21 0 (-3303780809))) (.leaf (.ubHLePi 0 0 0 129934788168))) (.node (.leaf (.ubHLePj 0 0 1 1801269821)) (.leaf (.ubHLePi 2 0 2 211741074604))))
            (.node (.node (.leaf (.ubHMcc 2 0 11 76000453431)) (.leaf (.ubHLePi 2 0 12 63503796729))) (.node (.leaf (.ubHLePi 2 1 1 106780906964)) (.leaf (.ubHMcc 2 1 7 124510897546))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 2 1 10 128593113319)) (.leaf (.ubHLePi 2 1 18 20613956756))) (.node (.leaf (.ubHLePi 2 2 0 27738647604)) (.leaf (.ubHMcc 2 2 1 37173680593))))
            (.node (.node (.leaf (.ubHLePi 2 2 7 30894970651)) (.leaf (.ubHMcc 2 2 11 28019371666))) (.node (.leaf (.ubHGe0 3 0 0 21052263014)) (.leaf (.ubHLePj 3 0 1 39449921086)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 3 0 18 36536106)) (.leaf (.ubHLePj 3 3 17 26203315329))) (.node (.leaf (.ubHLePi 4 4 0 2247445905)) (.leaf (.ubHGe0 4 4 17 6081374549))))
            (.node (.node (.leaf (.ubHGe0 5 0 5 6127535)) (.leaf (.ubHGe0 5 0 14 622296262))) (.node (.leaf (.ubHGe0 5 0 15 13290001)) (.leaf (.ubHLePj 5 1 0 3542994032))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePj 5 3 16 417419109)) (.node (.leaf (.ubHGe0 6 0 0 13012062539)) (.leaf (.ubHLePj 6 0 1 33333299497))))
            (.node (.node (.leaf (.ubHLePj 6 1 0 12545863528)) (.leaf (.ubHMcc 6 5 15 1881827037))) (.node (.leaf (.ubHLePi 6 6 0 263144030)) (.leaf (.ubHGe0 8 0 0 16637351987)))))
            (.node
            (.node (.node (.leaf (.ubHLePj 8 0 1 23254727577)) (.leaf (.ubHLePj 8 1 0 16135892060))) (.node (.leaf (.ubHLePi 8 8 0 5201889291)) (.leaf (.ubHLePj 8 8 1 1331814))))
            (.node (.node (.leaf (.ubHLePi 9 2 12 1159361595)) (.leaf (.ubHLePi 9 7 0 8471069))) (.node (.leaf (.ubHLePi 10 10 0 3617796012)) (.leaf (.ubHLePj 11 0 10 1956949))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHMcc 11 11 8 254802033)) (.leaf (.ubHLePi 11 11 10 978269366))) (.node (.leaf (.ubHGe0 12 0 0 14052169599)) (.leaf (.ubHLePj 12 0 1 15717170728))))
            (.node (.node (.leaf (.ubHLePi 12 0 7 182440679)) (.leaf (.ubHLePj 12 1 0 25038964479))) (.node (.leaf (.ubHMcc 12 2 9 623778450)) (.leaf (.ubHMcc 12 10 0 40339509)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 12 12 0 31409244)) (.leaf (.ubHLePi 12 12 2 62871864))) (.node (.leaf (.ubHLePj 12 12 8 1645127779)) (.leaf (.ubHLePi 13 13 0 114827043))))
            (.node (.node (.leaf (.ubHGe0 14 0 0 1457708385)) (.leaf (.ubHLePj 14 0 1 16154257868))) (.node (.leaf (.ubHLePj 14 13 0 43865770)) (.leaf (.ubHGe0 15 0 0 6245701366)))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePj 15 0 1 4003733416)) (.leaf (.ubHLePj 15 1 0 3089546024))) (.node (.leaf (.ubHLePj 15 4 6 19559485)) (.leaf (.ubHLePi 15 15 0 1267338100))))
            (.node (.node (.leaf (.ubHLePj 16 0 3 1596355945)) (.leaf (.ubHMcc 16 1 1 56744031077))) (.node (.leaf (.ubHGe0 16 2 5 752693094)) (.leaf (.ubHLePj 16 10 0 29300611)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 16 11 5 52158627)) (.leaf (.ubHGe0 16 14 0 197930563))) (.node (.leaf (.ubHLePj 16 14 5 141075553)) (.leaf (.ubHLePj 16 15 4 368993245))))
            (.node (.node (.leaf (.ubHLePj 16 16 2 89889154)) (.leaf (.ubHLePi 17 16 0 173372001))) (.node (.leaf (.ubHGe0 17 17 4 888635803)) (.leaf (.ubHGe0 18 0 0 4668921841))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePj 18 0 1 4321684342)) (.leaf (.ubHLePj 18 1 0 7029592608))) (.node (.leaf (.ubHLePi 18 18 0 1595528407)) (.leaf (.ubHLePj 19 0 1 26267470051))))
            (.node (.node (.leaf (.ubHMcc 19 0 2 2719890422)) (.leaf (.ubHLePj 19 1 0 31782625671))) (.node (.leaf (.ubHLePi 19 6 0 545539392)) (.leaf (.ubHMcc 19 9 1 143497373)))))
            (.node
            (.node (.node (.leaf (.ubHMcc 19 18 1 675281755)) (.leaf (.ubHMcc 20 6 0 7004590515))) (.node (.leaf (.ubHLePi 20 12 1 3677816570)) (.leaf (.ubHMcc 20 15 1 5409329809))))
            (.node (.node (.leaf (.ubHMcc 20 17 0 428004275)) (.leaf (.ubHLePi 20 18 1 3553100746))) (.node (.leaf (.ubHLePi 20 20 0 634744661)) (.leaf (.ubHGe0 0 0 6 11104)))))))))))
    (.node
      (.node
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 0 0 5 62259)) (.node (.leaf (.ubHGe0 0 0 4 146160)) (.leaf (.ubHLePi 0 0 3 183750))))
            (.node (.node (.leaf (.ubHGe0 0 0 2 130400)) (.leaf (.ubHLePi 0 0 1 49507))) (.node (.leaf (.ubHGe0 0 0 0 7853)) (.leaf (.ubHGe0 1 0 6 13734)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 1 1 5 5664)) (.leaf (.ubHLePi 1 0 5 82404))) (.node (.leaf (.ubHLePi 1 1 4 26482)) (.leaf (.ubHGe0 1 0 4 206010))))
            (.node (.node (.leaf (.ubHGe0 1 1 3 49743)) (.leaf (.ubHLePi 1 0 3 274680))) (.node (.leaf (.ubHLePi 1 1 2 46897)) (.leaf (.ubHGe0 1 0 2 206010))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 1 1 1 22181)) (.leaf (.ubHLePi 1 0 1 82404))) (.node (.leaf (.ubHLePi 1 1 0 4209)) (.leaf (.ubHGe0 1 0 0 13734))))
            (.node (.node (.leaf (.ubHLePi 2 0 6 8420)) (.leaf (.ubHLePi 2 1 5 5145))) (.node (.leaf (.ubHGe0 2 2 4 778)) (.leaf (.ubHGe0 2 0 5 51187)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 2 1 4 22023)) (.leaf (.ubHLePi 2 2 3 2909))) (.node (.leaf (.ubHLePi 2 0 4 128494)) (.leaf (.ubHLePi 2 1 3 37709))))
            (.node (.node (.leaf (.ubHGe0 2 2 2 4098)) (.leaf (.ubHGe0 2 0 3 170850))) (.node (.leaf (.ubHGe0 2 1 2 32220)) (.leaf (.ubHLePi 2 2 1 2576)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHGe0 2 2 0 609)) (.node (.leaf (.ubHGe0 2 0 1 50183)) (.leaf (.ubHGe0 2 1 0 2317))))
            (.node (.node (.leaf (.ubHLePi 2 0 0 8224)) (.leaf (.ubHGe0 3 0 6 5741))) (.node (.leaf (.ubHLePi 3 1 5 2239)) (.leaf (.ubHLePi 3 2 4 3817)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 3 3 3 427)) (.leaf (.ubHLePi 3 0 5 29945))) (.node (.leaf (.ubHGe0 3 1 4 17822)) (.leaf (.ubHGe0 3 2 3 15458))))
            (.node (.node (.leaf (.ubHGe0 3 3 2 1195)) (.leaf (.ubHGe0 3 0 4 61403))) (.node (.leaf (.ubHLePi 3 1 3 48356)) (.leaf (.ubHLePi 3 2 2 23440))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 3 3 1 1120)) (.leaf (.ubHLePi 3 0 3 61201))) (.node (.leaf (.ubHGe0 3 1 2 60625)) (.leaf (.ubHGe0 3 2 1 15778))))
            (.node (.node (.leaf (.ubHGe0 3 3 0 352)) (.leaf (.ubHGe0 3 0 2 28472))) (.node (.leaf (.ubHLePi 3 1 1 36266)) (.leaf (.ubHLePi 3 2 0 3979)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 3 0 1 3680)) (.leaf (.ubHGe0 3 1 0 8414))) (.node (.leaf (.ubHLePi 3 0 0 790)) (.leaf (.ubHLePi 4 0 6 643))))
            (.node (.node (.leaf (.ubHLePi 4 1 5 3702)) (.leaf (.ubHLePi 4 2 4 2271))) (.node (.leaf (.ubHLePi 4 3 3 308)) (.leaf (.ubHLePi 4 4 2 8))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHGe0 4 0 5 7739)) (.node (.leaf (.ubHGe0 4 1 4 22081)) (.leaf (.ubHGe0 4 2 3 9539))))
            (.node (.node (.leaf (.ubHGe0 4 3 2 924)) (.leaf (.ubHGe0 4 4 1 16))) (.node (.leaf (.ubHLePi 4 0 4 30056)) (.leaf (.ubHLePi 4 1 3 51408)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 4 2 2 14992)) (.leaf (.ubHLePi 4 3 1 924))) (.node (.leaf (.ubHGe0 4 0 3 55815)) (.leaf (.ubHGe0 4 1 2 58809))))
            (.node (.node (.leaf (.ubHGe0 4 2 1 10451)) (.leaf (.ubHGe0 4 3 0 308))) (.node (.leaf (.ubHLePi 4 0 2 54841)) (.leaf (.ubHLePi 4 1 1 33199))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 4 2 0 2727)) (.leaf (.ubHGe0 4 0 1 27627))) (.node (.leaf (.ubHGe0 4 1 0 7420)) (.leaf (.ubHLePi 4 0 0 5640))))
            (.node (.node (.leaf (.ubHLePi 5 0 6 2829)) (.leaf (.ubHLePi 5 1 5 4204))) (.node (.leaf (.ubHLePi 5 2 4 1661)) (.leaf (.ubHGe0 5 3 3 491)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 5 4 2 196)) (.leaf (.ubHGe0 5 5 1 10))) (.node (.leaf (.ubHGe0 5 1 4 22711)) (.leaf (.ubHGe0 5 2 3 4939))))
            (.node (.node (.leaf (.ubHLePi 5 3 2 2020)) (.leaf (.ubHLePi 5 4 1 401))) (.node (.leaf (.ubHLePi 5 5 0 9)) (.leaf (.ubHLePi 5 0 4 55837)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 5 1 3 47291)) (.node (.leaf (.ubHLePi 5 2 2 4352)) (.leaf (.ubHGe0 5 3 1 2554))))
            (.node (.node (.leaf (.ubHGe0 5 4 0 204)) (.leaf (.ubHGe0 5 0 3 84372))) (.node (.leaf (.ubHGe0 5 1 2 47435)) (.leaf (.ubHGe0 5 2 1 533)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 5 3 0 1027)) (.leaf (.ubHLePi 5 0 2 70680))) (.node (.leaf (.ubHLePi 5 1 1 22814)) (.leaf (.ubHGe0 5 2 0 541))))
            (.node (.node (.leaf (.ubHGe0 5 0 1 31041)) (.leaf (.ubHGe0 5 1 0 4164))) (.node (.leaf (.ubHLePi 5 0 0 5572)) (.leaf (.ubHLePi 6 0 6 7442))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 6 1 5 20174)) (.leaf (.ubHLePi 6 2 4 17013))) (.node (.leaf (.ubHLePi 6 3 3 5576)) (.leaf (.ubHLePi 6 4 2 672))))
            (.node (.node (.leaf (.ubHLePi 6 5 1 20)) (.leaf (.ubHGe0 6 0 5 60381))) (.node (.leaf (.ubHGe0 6 1 4 125738)) (.leaf (.ubHGe0 6 2 3 79155)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 6 3 2 18149)) (.leaf (.ubHGe0 6 4 1 1356))) (.node (.leaf (.ubHGe0 6 5 0 19)) (.leaf (.ubHLePi 6 0 4 200118))))
            (.node (.node (.leaf (.ubHLePi 6 1 3 309679)) (.leaf (.ubHLePi 6 2 2 136866))) (.node (.leaf (.ubHLePi 6 3 1 19584)) (.leaf (.ubHLePi 6 4 0 684)))))))))
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHGe0 6 0 3 347803)) (.node (.leaf (.ubHGe0 6 1 2 377081)) (.leaf (.ubHGe0 6 2 1 104331))))
            (.node (.node (.leaf (.ubHGe0 6 3 0 7012)) (.leaf (.ubHLePi 6 0 2 335019))) (.node (.leaf (.ubHLePi 6 1 1 227217)) (.leaf (.ubHLePi 6 2 0 29607)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 6 0 1 169852)) (.leaf (.ubHGe0 6 1 0 54250))) (.node (.leaf (.ubHLePi 6 0 0 35457)) (.leaf (.ubHLePi 7 0 6 514))))
            (.node (.node (.leaf (.ubHGe0 7 1 5 775)) (.leaf (.ubHLePi 7 2 4 5025))) (.node (.leaf (.ubHLePi 7 3 3 5914)) (.leaf (.ubHLePi 7 4 2 1904))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 7 5 1 177)) (.leaf (.ubHGe0 7 0 5 1895))) (.node (.leaf (.ubHGe0 7 1 4 6072)) (.leaf (.ubHGe0 7 2 3 35274))))
            (.node (.node (.leaf (.ubHGe0 7 3 2 23599)) (.leaf (.ubHGe0 7 4 1 4413))) (.node (.leaf (.ubHGe0 7 5 0 179)) (.leaf (.ubHLePi 7 0 4 6924)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 7 1 3 44868)) (.leaf (.ubHLePi 7 2 2 82595))) (.node (.leaf (.ubHLePi 7 3 1 30353)) (.leaf (.ubHLePi 7 4 0 2512))))
            (.node (.node (.leaf (.ubHGe0 7 0 3 22507)) (.leaf (.ubHGe0 7 1 2 94233))) (.node (.leaf (.ubHGe0 7 2 1 80205)) (.leaf (.ubHGe0 7 3 0 12673)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 7 0 2 38075)) (.node (.leaf (.ubHLePi 7 1 1 82341)) (.leaf (.ubHLePi 7 2 0 27861))))
            (.node (.node (.leaf (.ubHGe0 7 0 1 29983)) (.leaf (.ubHGe0 7 1 0 26129))) (.node (.leaf (.ubHLePi 7 0 0 8873)) (.leaf (.ubHLePi 8 0 6 794)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 8 1 5 1524)) (.leaf (.ubHLePi 8 2 4 2679))) (.node (.leaf (.ubHLePi 8 3 3 2551)) (.leaf (.ubHLePi 8 4 2 1144))))
            (.node (.node (.leaf (.ubHLePi 8 5 1 240)) (.leaf (.ubHLePi 8 6 0 3))) (.node (.leaf (.ubHGe0 8 0 5 5550)) (.leaf (.ubHGe0 8 1 4 12054))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 8 2 3 17199)) (.leaf (.ubHGe0 8 3 2 11387))) (.node (.leaf (.ubHGe0 8 4 1 3209)) (.leaf (.ubHGe0 8 5 0 256))))
            (.node (.node (.leaf (.ubHLePi 8 0 4 18087)) (.leaf (.ubHLePi 8 1 3 38681))) (.node (.leaf (.ubHLePi 8 2 2 40245)) (.leaf (.ubHLePi 8 3 1 16616)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 8 4 0 2097)) (.leaf (.ubHGe0 8 0 3 34273))) (.node (.leaf (.ubHGe0 8 1 2 61661)) (.leaf (.ubHGe0 8 2 1 40873))))
            (.node (.node (.leaf (.ubHGe0 8 3 0 7816)) (.leaf (.ubHLePi 8 0 2 38527))) (.node (.leaf (.ubHLePi 8 1 1 48425)) (.leaf (.ubHLePi 8 2 0 15170))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHGe0 8 0 1 23685)) (.node (.leaf (.ubHGe0 8 1 0 14922)) (.leaf (.ubHLePi 8 0 0 6102))))
            (.node (.node (.leaf (.ubHGe0 9 0 6 892)) (.leaf (.ubHGe0 9 1 5 2812))) (.node (.leaf (.ubHGe0 9 2 4 4453)) (.leaf (.ubHGe0 9 3 3 2932)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 9 4 2 682)) (.leaf (.ubHLePi 9 5 1 24))) (.node (.leaf (.ubHLePi 9 6 0 12)) (.leaf (.ubHLePi 9 0 5 7325))))
            (.node (.node (.leaf (.ubHLePi 9 1 4 21106)) (.leaf (.ubHLePi 9 2 3 24507))) (.node (.leaf (.ubHLePi 9 3 2 10570)) (.leaf (.ubHLePi 9 4 1 1130))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 9 5 0 80)) (.leaf (.ubHGe0 9 0 4 26419))) (.node (.leaf (.ubHGe0 9 1 3 61800)) (.leaf (.ubHGe0 9 2 2 48727))))
            (.node (.node (.leaf (.ubHGe0 9 3 1 11828)) (.leaf (.ubHGe0 9 4 0 331))) (.node (.leaf (.ubHLePi 9 0 3 51713)) (.leaf (.ubHLePi 9 1 2 87838)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 9 2 1 41228)) (.leaf (.ubHLePi 9 3 0 4057))) (.node (.leaf (.ubHGe0 9 0 2 56709)) (.leaf (.ubHGe0 9 1 1 60393))))
            (.node (.node (.leaf (.ubHGe0 9 2 0 12468)) (.leaf (.ubHLePi 9 0 1 32631))) (.node (.leaf (.ubHLePi 9 1 0 16031)) (.leaf (.ubHGe0 9 0 0 7645)))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 10 0 6 282)) (.leaf (.ubHLePi 10 1 5 1807))) (.node (.leaf (.ubHLePi 10 2 4 4846)) (.leaf (.ubHLePi 10 3 3 3688))))
            (.node (.node (.leaf (.ubHGe0 10 4 2 102)) (.leaf (.ubHGe0 10 5 1 811))) (.node (.leaf (.ubHGe0 10 6 0 179)) (.leaf (.ubHGe0 10 0 5 3187)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 10 1 4 17559)) (.leaf (.ubHGe0 10 2 3 28795))) (.node (.leaf (.ubHGe0 10 3 2 10520)) (.leaf (.ubHLePi 10 4 1 3665))))
            (.node (.node (.leaf (.ubHLePi 10 5 0 1682)) (.leaf (.ubHLePi 10 0 4 15619))) (.node (.leaf (.ubHLePi 10 1 3 60337)) (.leaf (.ubHLePi 10 2 2 56390))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 10 3 1 3924)) (.leaf (.ubHGe0 10 4 0 5394))) (.node (.leaf (.ubHGe0 10 0 3 38576)) (.leaf (.ubHGe0 10 1 2 93077))))
            (.node (.node (.leaf (.ubHGe0 10 2 1 40396)) (.leaf (.ubHLePi 10 3 0 5013))) (.node (.leaf (.ubHLePi 10 0 2 49518)) (.leaf (.ubHLePi 10 1 1 63922)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 10 2 0 6568)) (.leaf (.ubHGe0 10 0 1 31094))) (.node (.leaf (.ubHGe0 10 1 0 14935)) (.leaf (.ubHLePi 10 0 0 7364))))
            (.node (.node (.leaf (.ubHGe0 11 0 6 220)) (.leaf (.ubHGe0 11 1 5 1573))) (.node (.leaf (.ubHGe0 11 2 4 3797)) (.leaf (.ubHGe0 11 3 3 4265))))))))))
      (.node
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHGe0 11 4 2 2097)) (.node (.leaf (.ubHGe0 11 5 1 339)) (.leaf (.ubHLePi 11 6 0 297))))
            (.node (.node (.leaf (.ubHLePi 11 0 5 2650)) (.leaf (.ubHLePi 11 1 4 14403))) (.node (.leaf (.ubHLePi 11 2 3 26727)) (.leaf (.ubHLePi 11 3 2 20810)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 11 4 1 5970)) (.leaf (.ubHGe0 11 5 0 1114))) (.node (.leaf (.ubHGe0 11 0 4 12870)) (.leaf (.ubHGe0 11 1 3 52567))))
            (.node (.node (.leaf (.ubHGe0 11 2 2 68903)) (.leaf (.ubHGe0 11 3 1 32371))) (.node (.leaf (.ubHGe0 11 4 0 813)) (.leaf (.ubHLePi 11 0 3 32707))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 11 1 2 94304)) (.leaf (.ubHLePi 11 2 1 76245))) (.node (.leaf (.ubHLePi 11 3 0 12301)) (.leaf (.ubHGe0 11 0 2 45829))))
            (.node (.node (.leaf (.ubHGe0 11 1 1 82293)) (.leaf (.ubHGe0 11 2 0 27946))) (.node (.leaf (.ubHLePi 11 0 1 33398)) (.leaf (.ubHLePi 11 1 0 26896)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 11 0 0 9711)) (.leaf (.ubHGe0 12 0 6 33))) (.node (.leaf (.ubHGe0 12 1 5 1058)) (.leaf (.ubHGe0 12 2 4 6028))))
            (.node (.node (.leaf (.ubHGe0 12 3 3 12763)) (.leaf (.ubHGe0 12 4 2 11603))) (.node (.leaf (.ubHGe0 12 5 1 4331)) (.leaf (.ubHGe0 12 6 0 646)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 12 0 5 1192)) (.node (.leaf (.ubHLePi 12 1 4 16199)) (.leaf (.ubHLePi 12 2 3 58124))))
            (.node (.node (.leaf (.ubHLePi 12 3 2 78876)) (.leaf (.ubHLePi 12 4 1 41869))) (.node (.leaf (.ubHLePi 12 5 0 7615)) (.leaf (.ubHGe0 12 0 4 10429)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 12 1 3 84776)) (.leaf (.ubHGe0 12 2 2 192263))) (.node (.leaf (.ubHGe0 12 3 1 152254)) (.leaf (.ubHGe0 12 4 0 37387))))
            (.node (.node (.leaf (.ubHLePi 12 0 3 39697)) (.leaf (.ubHLePi 12 1 2 200115))) (.node (.leaf (.ubHLePi 12 2 1 263516)) (.leaf (.ubHLePi 12 3 0 94525))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 12 0 2 75304)) (.leaf (.ubHGe0 12 1 1 218616))) (.node (.leaf (.ubHGe0 12 2 0 128979)) (.leaf (.ubHLePi 12 0 1 69878))))
            (.node (.node (.leaf (.ubHLePi 12 1 0 90174)) (.leaf (.ubHGe0 13 0 6 39))) (.node (.leaf (.ubHGe0 13 1 5 450)) (.leaf (.ubHGe0 13 2 4 1793)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 13 3 3 3808)) (.leaf (.ubHGe0 13 4 2 4728))) (.node (.leaf (.ubHGe0 13 5 1 2784)) (.leaf (.ubHGe0 13 6 0 1502))))
            (.node (.node (.leaf (.ubHLePi 13 0 5 603)) (.leaf (.ubHLePi 13 1 4 5239))) (.node (.leaf (.ubHLePi 13 2 3 16894)) (.leaf (.ubHLePi 13 3 2 27760))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 13 4 1 21501)) (.node (.leaf (.ubHLePi 13 5 0 10602)) (.leaf (.ubHGe0 13 0 4 3731))))
            (.node (.node (.leaf (.ubHGe0 13 1 3 24994)) (.leaf (.ubHGe0 13 2 2 61617))) (.node (.leaf (.ubHGe0 13 3 1 65415)) (.leaf (.ubHGe0 13 4 0 34051)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 13 0 3 12211)) (.leaf (.ubHLePi 13 1 2 61047))) (.node (.leaf (.ubHLePi 13 2 1 98879)) (.leaf (.ubHLePi 13 3 0 62117))))
            (.node (.node (.leaf (.ubHGe0 13 0 2 22651)) (.leaf (.ubHGe0 13 1 1 74523))) (.node (.leaf (.ubHGe0 13 2 0 66403)) (.leaf (.ubHLePi 13 0 1 22408))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 13 1 0 38817)) (.leaf (.ubHGe0 13 0 0 9589))) (.node (.leaf (.ubHLePi 14 0 6 1)) (.leaf (.ubHLePi 14 1 5 36))))
            (.node (.node (.leaf (.ubHLePi 14 2 4 39)) (.leaf (.ubHGe0 14 3 3 242))) (.node (.leaf (.ubHGe0 14 4 2 1753)) (.leaf (.ubHGe0 14 5 1 3442)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 14 6 0 1334)) (.leaf (.ubHGe0 14 0 5 36))) (.node (.leaf (.ubHGe0 14 1 4 176)) (.leaf (.ubHLePi 14 2 3 613))))
            (.node (.node (.leaf (.ubHLePi 14 3 2 7089)) (.leaf (.ubHLePi 14 4 1 18902))) (.node (.leaf (.ubHLePi 14 5 0 10519)) (.leaf (.ubHLePi 14 0 4 137)))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 14 1 3 380)) (.leaf (.ubHGe0 14 2 2 10746))) (.node (.leaf (.ubHGe0 14 3 1 41304)) (.leaf (.ubHGe0 14 4 0 33011))))
            (.node (.node (.leaf (.ubHLePi 14 0 3 9)) (.leaf (.ubHLePi 14 1 2 7145))) (.node (.leaf (.ubHLePi 14 2 1 44946)) (.leaf (.ubHLePi 14 3 0 53635)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 14 0 2 1735)) (.leaf (.ubHGe0 14 1 1 24342))) (.node (.leaf (.ubHGe0 14 2 0 48012)) (.leaf (.ubHLePi 14 0 1 5240))))
            (.node (.node (.leaf (.ubHLePi 14 1 0 22570)) (.leaf (.ubHLePi 15 0 6 1))) (.node (.leaf (.ubHLePi 15 1 5 54)) (.leaf (.ubHLePi 15 2 4 669))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 15 3 3 3852)) (.leaf (.ubHLePi 15 4 2 10374))) (.node (.leaf (.ubHLePi 15 5 1 11036)) (.leaf (.ubHLePi 15 6 0 4947))))
            (.node (.node (.leaf (.ubHGe0 15 0 5 53)) (.leaf (.ubHGe0 15 1 4 1454))) (.node (.leaf (.ubHGe0 15 2 3 13172)) (.leaf (.ubHGe0 15 3 2 49503)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 15 4 1 71019)) (.leaf (.ubHGe0 15 5 0 37876))) (.node (.leaf (.ubHLePi 15 0 4 785)) (.leaf (.ubHLePi 15 1 3 14943))))
            (.node (.node (.leaf (.ubHLePi 15 2 2 88049)) (.leaf (.ubHLePi 15 3 1 179860))) (.node (.leaf (.ubHLePi 15 4 0 121894)) (.leaf (.ubHGe0 15 0 3 5623)))))))))
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHGe0 15 1 2 69196)) (.node (.leaf (.ubHGe0 15 2 1 224769)) (.leaf (.ubHGe0 15 3 0 209319))))
            (.node (.node (.leaf (.ubHLePi 15 0 2 20276)) (.leaf (.ubHLePi 15 1 1 138898))) (.node (.leaf (.ubHLePi 15 2 0 201366)) (.leaf (.ubHGe0 15 0 1 34006)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 15 1 0 102657)) (.leaf (.ubHLePi 15 0 0 21646))) (.node (.leaf (.ubHLePi 16 1 5 3)) (.leaf (.ubHLePi 16 2 4 53))))
            (.node (.node (.leaf (.ubHGe0 16 3 3 55)) (.leaf (.ubHGe0 16 4 2 1637))) (.node (.leaf (.ubHGe0 16 5 1 3234)) (.leaf (.ubHLePi 16 6 0 1570))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 16 0 5 3)) (.leaf (.ubHGe0 16 1 4 117))) (.node (.leaf (.ubHGe0 16 2 3 82)) (.leaf (.ubHLePi 16 3 2 6236))))
            (.node (.node (.leaf (.ubHLePi 16 4 1 18361)) (.leaf (.ubHGe0 16 5 0 5101))) (.node (.leaf (.ubHLePi 16 0 4 63)) (.leaf (.ubHLePi 16 1 3 329)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 16 2 2 8576)) (.leaf (.ubHGe0 16 3 1 40542))) (.node (.leaf (.ubHLePi 16 4 0 1991)) (.leaf (.ubHGe0 16 0 3 192))))
            (.node (.node (.leaf (.ubHLePi 16 1 2 5003)) (.leaf (.ubHLePi 16 2 1 43682))) (.node (.leaf (.ubHLePi 16 3 0 11694)) (.leaf (.ubHGe0 16 0 2 1025)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHGe0 16 1 1 23011)) (.node (.leaf (.ubHGe0 16 2 0 19496)) (.leaf (.ubHLePi 16 0 1 4743))))
            (.node (.node (.leaf (.ubHLePi 16 1 0 12038)) (.leaf (.ubHGe0 16 0 0 2695))) (.node (.leaf (.ubHGe0 17 2 4 77)) (.leaf (.ubHGe0 17 3 3 1816)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 17 4 2 11469)) (.leaf (.ubHGe0 17 5 1 23790))) (.node (.leaf (.ubHGe0 17 6 0 16142)) (.leaf (.ubHLePi 17 1 4 146))))
            (.node (.node (.leaf (.ubHLePi 17 2 3 5392)) (.leaf (.ubHLePi 17 3 2 47884))) (.node (.leaf (.ubHLePi 17 4 1 132338)) (.leaf (.ubHLePi 17 5 0 112390))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 17 0 4 69)) (.leaf (.ubHGe0 17 1 3 5342))) (.node (.leaf (.ubHGe0 17 2 2 74910)) (.leaf (.ubHGe0 17 3 1 292854))))
            (.node (.node (.leaf (.ubHGe0 17 4 0 324981)) (.leaf (.ubHLePi 17 0 3 1766))) (.node (.leaf (.ubHLePi 17 1 2 52032)) (.leaf (.ubHLePi 17 2 1 322475)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 17 3 0 499124)) (.leaf (.ubHGe0 17 0 2 13538))) (.node (.leaf (.ubHGe0 17 1 1 176784)) (.leaf (.ubHGe0 17 2 0 429288))))
            (.node (.node (.leaf (.ubHLePi 17 0 1 38615)) (.leaf (.ubHLePi 17 1 0 196025))) (.node (.leaf (.ubHGe0 17 0 0 37128)) (.leaf (.ubHGe0 18 3 3 300))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHGe0 18 4 2 5655)) (.node (.leaf (.ubHGe0 18 5 1 23054)) (.leaf (.ubHGe0 18 6 0 12895))))
            (.node (.node (.leaf (.ubHLePi 18 2 3 857)) (.leaf (.ubHLePi 18 3 2 22083))) (.node (.leaf (.ubHLePi 18 4 1 118224)) (.leaf (.ubHLePi 18 5 0 94258)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 18 1 3 815)) (.leaf (.ubHGe0 18 2 2 32424))) (.node (.leaf (.ubHGe0 18 3 1 242633)) (.leaf (.ubHGe0 18 4 0 277449))))
            (.node (.node (.leaf (.ubHLePi 18 0 3 259)) (.leaf (.ubHLePi 18 1 2 21207))) (.node (.leaf (.ubHLePi 18 2 1 249019)) (.leaf (.ubHLePi 18 3 0 425598))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 18 0 2 5211)) (.leaf (.ubHGe0 18 1 1 127778))) (.node (.leaf (.ubHGe0 18 2 0 361152)) (.leaf (.ubHLePi 18 0 1 26221))))
            (.node (.node (.leaf (.ubHLePi 18 1 0 161400)) (.leaf (.ubHLePi 19 4 2 1960))) (.node (.leaf (.ubHLePi 19 5 1 16895)) (.leaf (.ubHGe0 19 3 2 7287)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 19 4 1 82032)) (.leaf (.ubHGe0 19 5 0 189331))) (.node (.leaf (.ubHLePi 19 2 2 10208)) (.leaf (.ubHLePi 19 3 1 159864))))
            (.node (.node (.leaf (.ubHLePi 19 4 0 478612)) (.leaf (.ubHGe0 19 1 2 6384))) (.node (.leaf (.ubHGe0 19 2 1 156216)) (.leaf (.ubHGe0 19 3 0 646707)))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 19 0 2 1503)) (.leaf (.ubHLePi 19 1 1 76508))) (.node (.leaf (.ubHLePi 19 2 0 492351)) (.leaf (.ubHGe0 19 0 1 15019))))
            (.node (.node (.leaf (.ubHGe0 19 1 0 200160)) (.leaf (.ubHLePi 19 0 0 33936))) (.node (.leaf (.ubHGe0 20 5 1 9768)) (.leaf (.ubHGe0 20 6 0 28193)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 20 4 1 45373)) (.leaf (.ubHLePi 20 5 0 166024))) (.node (.leaf (.ubHGe0 20 3 1 84774)) (.leaf (.ubHGe0 20 4 0 408481))))
            (.node (.node (.leaf (.ubHLePi 20 2 1 79566)) (.leaf (.ubHLePi 20 3 0 537173))) (.node (.leaf (.ubHGe0 20 1 1 37489)) (.leaf (.ubHGe0 20 2 0 398055))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 20 0 1 7090)) (.leaf (.ubHLePi 20 1 0 157542))) (.node (.leaf (.ubHGe0 20 0 0 26011)) (.leaf (.ubHLePi 21 6 0 22290))))
            (.node (.node (.leaf (.ubHGe0 21 5 0 124231)) (.leaf (.ubHLePi 21 4 0 290010))) (.node (.leaf (.ubHGe0 21 3 0 362703)) (.leaf (.ubHLePi 21 2 0 256163)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 21 1 0 96824)) (.leaf (.ubHLePi 21 0 0 15296))) (.node (.leaf (.ubPHi 6 272862)) (.leaf (.ubPHi 5 1171072))))
            (.node (.node (.leaf (.ubPHi 4 3510590)) (.leaf (.ubPHi 3 3363311))) (.node (.leaf (.ubPHi 2 3082552)) (.leaf (.eqP0 (-183208)))))))))))))

lemma step2aScale_pos : 0 < step2aScale := by decide
lemma step2aLb_strict : 209 * (step2aScale : ℤ) < 210 * step2aLb := by decide
lemma step2aCert_u_ok :
    checkBinoBoundU 21 6 [(2, 1), (20, 1), (21, 0)] step2aCert 19 1 step2aScale step2aLb = true := by
  decide
private lemma step2aCert_c_0 : checkBinoCForJ 21 6 0 step2aCert = true := by decide
private lemma step2aCert_c_1 : checkBinoCForJ 21 6 1 step2aCert = true := by decide
private lemma step2aCert_c_2 : checkBinoCForJ 21 6 2 step2aCert = true := by decide
private lemma step2aCert_c_3 : checkBinoCForJ 21 6 3 step2aCert = true := by decide
private lemma step2aCert_c_4 : checkBinoCForJ 21 6 4 step2aCert = true := by decide
private lemma step2aCert_c_5 : checkBinoCForJ 21 6 5 step2aCert = true := by decide
private lemma step2aCert_c_6 : checkBinoCForJ 21 6 6 step2aCert = true := by decide
private lemma step2aCert_c_7 : checkBinoCForJ 21 6 7 step2aCert = true := by decide
private lemma step2aCert_c_8 : checkBinoCForJ 21 6 8 step2aCert = true := by decide
private lemma step2aCert_c_9 : checkBinoCForJ 21 6 9 step2aCert = true := by decide
private lemma step2aCert_c_10 : checkBinoCForJ 21 6 10 step2aCert = true := by decide
private lemma step2aCert_c_11 : checkBinoCForJ 21 6 11 step2aCert = true := by decide
private lemma step2aCert_c_12 : checkBinoCForJ 21 6 12 step2aCert = true := by decide
private lemma step2aCert_c_13 : checkBinoCForJ 21 6 13 step2aCert = true := by decide
private lemma step2aCert_c_14 : checkBinoCForJ 21 6 14 step2aCert = true := by decide
private lemma step2aCert_c_15 : checkBinoCForJ 21 6 15 step2aCert = true := by decide
private lemma step2aCert_c_16 : checkBinoCForJ 21 6 16 step2aCert = true := by decide
private lemma step2aCert_c_17 : checkBinoCForJ 21 6 17 step2aCert = true := by decide
private lemma step2aCert_c_18 : checkBinoCForJ 21 6 18 step2aCert = true := by decide
private lemma step2aCert_c_19 : checkBinoCForJ 21 6 19 step2aCert = true := by decide
private lemma step2aCert_c_20 : checkBinoCForJ 21 6 20 step2aCert = true := by decide
private lemma step2aCert_c_21 : checkBinoCForJ 21 6 21 step2aCert = true := by decide
lemma step2aCert_c_ok : ∀ j ≤ 21, checkBinoCForJ 21 6 j step2aCert = true := by
  intro j hj
  match j with
  | 0 => exact step2aCert_c_0
  | 1 => exact step2aCert_c_1
  | 2 => exact step2aCert_c_2
  | 3 => exact step2aCert_c_3
  | 4 => exact step2aCert_c_4
  | 5 => exact step2aCert_c_5
  | 6 => exact step2aCert_c_6
  | 7 => exact step2aCert_c_7
  | 8 => exact step2aCert_c_8
  | 9 => exact step2aCert_c_9
  | 10 => exact step2aCert_c_10
  | 11 => exact step2aCert_c_11
  | 12 => exact step2aCert_c_12
  | 13 => exact step2aCert_c_13
  | 14 => exact step2aCert_c_14
  | 15 => exact step2aCert_c_15
  | 16 => exact step2aCert_c_16
  | 17 => exact step2aCert_c_17
  | 18 => exact step2aCert_c_18
  | 19 => exact step2aCert_c_19
  | 20 => exact step2aCert_c_20
  | 21 => exact step2aCert_c_21
  | _ + 22 => omega

def step2bScale : ℕ := 50000000000
def step2bLb : ℤ := 31519529442
def step2bCert : BinTree BinoStep :=
  (.node
    (.node
      (.node
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.eqP1 (-1777255467403))) (.node (.leaf (.eqB00 0 592100073843)) (.leaf (.eqDiag 2 32646566082))))
            (.node (.node (.leaf (.eqB00 2 (-296782176158))) (.leaf (.eqB10 2 408561844867))) (.node (.leaf (.eqB01 2 518757597717)) (.leaf (.eqDiag 3 25132212335)))))
            (.node
            (.node (.node (.leaf (.eqB00 3 (-696516688853))) (.leaf (.eqB01 3 1280249662693))) (.node (.leaf (.eqDiag 4 35066327069)) (.leaf (.eqB10 5 224506951647))))
            (.node (.node (.leaf (.eqB00 6 (-31496775694))) (.leaf (.eqB10 6 240570932473))) (.node (.leaf (.eqDiag 7 134857849759)) (.leaf (.eqB00 7 (-716126530630)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqB10 7 596923329839)) (.leaf (.eqB01 7 982581118011))) (.node (.leaf (.eqDiag 8 192657412253)) (.leaf (.eqB00 8 (-1097134692449)))))
            (.node (.node (.leaf (.eqB10 8 1185767369399)) (.leaf (.eqB01 8 1691269879458))) (.node (.leaf (.eqDiag 10 673406307716)) (.leaf (.eqB00 10 (-284399676176))))))
            (.node
            (.node (.node (.leaf (.eqB10 10 43433299166)) (.leaf (.eqB01 10 519403165333))) (.node (.leaf (.eqB10 11 222904189751)) (.leaf (.eqDiag 12 104103561367))))
            (.node (.node (.leaf (.eqB00 12 (-75274339555))) (.leaf (.eqB10 12 318900120203))) (.node (.leaf (.eqB01 12 134748236687)) (.leaf (.eqB00 13 (-66468263793))))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.eqB01 13 111394662916)) (.node (.leaf (.eqB01 14 215792729301)) (.leaf (.eqDiag 15 60612203459))))
            (.node (.node (.leaf (.eqB00 16 (-290916944319))) (.leaf (.eqB10 16 467805341454))) (.node (.leaf (.eqB01 16 188830966976)) (.leaf (.eqDiag 17 70265465545)))))
            (.node
            (.node (.node (.leaf (.eqB00 17 (-532367036686))) (.leaf (.eqB10 17 1339401602086))) (.node (.leaf (.eqB01 17 193131157208)) (.leaf (.eqDiag 19 42193201279))))
            (.node (.node (.leaf (.eqB00 19 (-716572702946))) (.leaf (.eqB01 19 1037942884138))) (.node (.leaf (.eqB10 20 1624107978343)) (.leaf (.eqB01 20 541380478987))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqB00 21 (-145481834746))) (.leaf (.eqSym 0 5 0 (-88973206241)))) (.node (.leaf (.eqSym 0 9 0 104850579745)) (.leaf (.eqSym 0 15 0 (-158174588873)))))
            (.node (.node (.leaf (.eqSym 0 19 0 624373377131)) (.leaf (.eqSym 0 20 0 (-762870744422)))) (.node (.leaf (.eqSym 0 21 0 247147795114)) (.leaf (.eqSym 1 2 1 (-337109380161))))))
            (.node
            (.node (.node (.leaf (.eqSym 1 3 1 370882286813)) (.leaf (.eqSym 1 5 1 (-157624971896)))) (.node (.leaf (.eqSym 1 9 1 61412326713)) (.leaf (.eqSym 1 11 1 (-28022217226)))))
            (.node (.node (.leaf (.eqSym 1 20 1 2523813541)) (.leaf (.eqSym 1 21 1 (-1659210230)))) (.node (.leaf (.eqSym 2 3 1 (-626323450892))) (.leaf (.eqSym 2 3 2 14712530477))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 2 4 1 1433763951927)) (.node (.leaf (.eqSym 2 4 2 135301744976)) (.leaf (.eqSym 2 5 2 (-277009797197)))))
            (.node (.node (.leaf (.eqSym 2 6 0 192040554113)) (.leaf (.eqSym 2 6 1 (-223194192731)))) (.node (.leaf (.eqSym 2 6 2 (-50654680291))) (.leaf (.eqSym 2 7 1 (-609658400353))))))
            (.node
            (.node (.node (.leaf (.eqSym 2 9 0 81371862695)) (.leaf (.eqSym 2 11 1 (-410159776121)))) (.node (.leaf (.eqSym 2 11 2 391893044152)) (.leaf (.eqSym 2 12 1 (-591544131503)))))
            (.node (.node (.leaf (.eqSym 2 13 1 1439603672264)) (.leaf (.eqSym 2 14 0 (-474979105248)))) (.node (.leaf (.eqSym 2 15 1 40519415208)) (.leaf (.eqSym 2 16 1 (-238046584024)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 2 17 0 548308503710)) (.leaf (.eqSym 2 17 1 496015612533))) (.node (.leaf (.eqSym 2 17 2 (-1028388698958))) (.leaf (.eqSym 2 19 0 (-233373184647)))))
            (.node (.node (.leaf (.eqSym 2 19 1 (-1666100245413))) (.leaf (.eqSym 2 19 2 1141700254178))) (.node (.leaf (.eqSym 2 20 1 971946718650)) (.leaf (.eqSym 2 21 2 (-351593869762))))))
            (.node
            (.node (.node (.leaf (.eqSym 3 4 0 717326050867)) (.leaf (.eqSym 3 4 1 (-22818525352)))) (.node (.leaf (.eqSym 3 5 0 388884354974)) (.leaf (.eqSym 3 5 1 447727604917))))
            (.node (.node (.leaf (.eqSym 3 5 2 (-308420764853))) (.leaf (.eqSym 3 5 3 225489907104))) (.node (.leaf (.eqSym 3 8 1 (-3396722257810))) (.leaf (.eqSym 3 8 2 149113567830)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 3 8 3 (-712639651797))) (.node (.leaf (.eqSym 3 9 0 (-530499232318))) (.leaf (.eqSym 3 9 1 837617454901))))
            (.node (.node (.leaf (.eqSym 3 9 2 1633050860863)) (.leaf (.eqSym 3 10 0 (-878340477722)))) (.node (.leaf (.eqSym 3 10 1 355164668325)) (.leaf (.eqSym 3 10 3 659822932543)))))
            (.node
            (.node (.node (.leaf (.eqSym 3 11 0 629255999361)) (.leaf (.eqSym 3 11 1 3163105755084))) (.node (.leaf (.eqSym 3 11 2 (-1770450545882))) (.leaf (.eqSym 3 12 3 (-128836978196)))))
            (.node (.node (.leaf (.eqSym 3 13 1 (-1183580245367))) (.leaf (.eqSym 3 14 0 402396694667))) (.node (.leaf (.eqSym 3 15 1 199627178008)) (.leaf (.eqSym 3 17 0 (-84279321918)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 3 17 1 (-2452276205017))) (.leaf (.eqSym 3 17 2 (-1203658233125)))) (.node (.leaf (.eqSym 3 18 0 (-61457494178))) (.leaf (.eqSym 3 18 1 1796441310414))))
            (.node (.node (.leaf (.eqSym 3 18 2 2323098999511)) (.leaf (.eqSym 3 19 1 272097817))) (.node (.leaf (.eqSym 3 19 2 37046351228)) (.leaf (.eqSym 3 19 3 720202400129)))))
            (.node
            (.node (.node (.leaf (.eqSym 3 20 2 (-845067705095))) (.leaf (.eqSym 3 20 3 (-1430067472743)))) (.node (.leaf (.eqSym 3 21 3 691161075294)) (.leaf (.eqSym 4 5 2 194930924360))))
            (.node (.node (.leaf (.eqSym 4 7 0 (-297570434074))) (.leaf (.eqSym 4 7 4 175632858183))) (.node (.leaf (.eqSym 4 8 4 104308203421)) (.leaf (.eqSym 4 9 1 899147910036)))))))))
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 4 9 2 833790667563)) (.node (.leaf (.eqSym 4 10 0 377697104131)) (.leaf (.eqSym 4 10 4 (-559413451337)))))
            (.node (.node (.leaf (.eqSym 4 11 2 (-1410795535553))) (.leaf (.eqSym 4 13 1 (-764123451527)))) (.node (.leaf (.eqSym 4 13 4 265353552396)) (.leaf (.eqSym 4 14 0 (-134556595154))))))
            (.node
            (.node (.node (.leaf (.eqSym 4 14 4 215029039600)) (.leaf (.eqSym 4 15 0 49413561752))) (.node (.leaf (.eqSym 4 17 0 (-11317545902))) (.leaf (.eqSym 4 17 1 210276564953))))
            (.node (.node (.leaf (.eqSym 4 17 2 2644018155113)) (.leaf (.eqSym 4 18 2 (-2768481977881)))) (.node (.leaf (.eqSym 4 19 2 641839511374)) (.leaf (.eqSym 4 19 4 (-527378955341)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 4 20 4 361535080146)) (.leaf (.eqSym 5 6 1 163077726324))) (.node (.leaf (.eqSym 5 6 3 (-360443505437))) (.leaf (.eqSym 5 6 5 5263121113))))
            (.node (.node (.leaf (.eqSym 5 8 0 (-879207505052))) (.leaf (.eqSym 5 8 1 1628409309060))) (.node (.leaf (.eqSym 5 8 3 693279536436)) (.leaf (.eqSym 5 8 4 746313520661)))))
            (.node
            (.node (.node (.leaf (.eqSym 5 8 5 (-423407746633))) (.leaf (.eqSym 5 9 0 877260735905))) (.node (.leaf (.eqSym 5 9 2 (-1566192703526))) (.leaf (.eqSym 5 9 5 375745127067))))
            (.node (.node (.leaf (.eqSym 5 10 4 (-2173472118730))) (.leaf (.eqSym 5 10 5 256245535535))) (.node (.leaf (.eqSym 5 11 0 329440089508)) (.leaf (.eqSym 5 11 1 (-2537089647282))))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 5 11 2 1127156017323)) (.node (.leaf (.eqSym 5 11 4 2017071780782)) (.leaf (.eqSym 5 11 5 (-327143822132)))))
            (.node (.node (.leaf (.eqSym 5 12 0 (-339007772342))) (.leaf (.eqSym 5 12 1 912914413716))) (.node (.leaf (.eqSym 5 12 3 95759989282)) (.leaf (.eqSym 5 13 1 459906267078)))))
            (.node
            (.node (.node (.leaf (.eqSym 5 13 4 (-774487712284))) (.leaf (.eqSym 5 15 1 (-180291395219)))) (.node (.leaf (.eqSym 5 15 2 (-41264358814))) (.leaf (.eqSym 5 16 1 67682910991))))
            (.node (.node (.leaf (.eqSym 5 16 4 (-45949210418))) (.leaf (.eqSym 5 16 5 (-453829752565)))) (.node (.leaf (.eqSym 5 17 5 1130094912141)) (.leaf (.eqSym 5 18 2 89801407327))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 5 19 3 (-202906774504))) (.leaf (.eqSym 5 19 4 230523739989))) (.node (.leaf (.eqSym 5 19 5 (-1015369353585))) (.leaf (.eqSym 6 7 3 (-603470421891)))))
            (.node (.node (.leaf (.eqSym 6 7 5 (-728634247700))) (.leaf (.eqSym 6 8 1 703696184371))) (.node (.leaf (.eqSym 6 8 3 (-118639929843))) (.leaf (.eqSym 6 8 5 308774030565)))))
            (.node
            (.node (.node (.leaf (.eqSym 6 9 0 (-76430466668))) (.leaf (.eqSym 6 9 5 1281054393861))) (.node (.leaf (.eqSym 6 9 6 (-189448695035))) (.leaf (.eqSym 6 11 1 (-471536351852)))))
            (.node (.node (.leaf (.eqSym 6 11 2 (-308687853212))) (.leaf (.eqSym 6 11 5 (-907810081048)))) (.node (.leaf (.eqSym 6 12 0 238530326706)) (.leaf (.eqSym 6 12 1 (-577411075748)))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 6 12 3 604937609459)) (.node (.leaf (.eqSym 6 13 0 (-20563957353))) (.leaf (.eqSym 6 13 1 452756846963))))
            (.node (.node (.leaf (.eqSym 6 13 4 (-53034566024))) (.leaf (.eqSym 6 13 6 113215838868))) (.node (.leaf (.eqSym 6 14 0 (-117324385885))) (.leaf (.eqSym 6 14 2 258033172921)))))
            (.node
            (.node (.node (.leaf (.eqSym 6 14 3 299611937616)) (.leaf (.eqSym 6 15 1 84469283290))) (.node (.leaf (.eqSym 6 15 3 (-179223108931))) (.leaf (.eqSym 6 16 1 (-11520420957)))))
            (.node (.node (.leaf (.eqSym 6 16 3 (-363659591848))) (.leaf (.eqSym 6 19 4 53034566024))) (.node (.leaf (.eqSym 6 19 5 51879025435)) (.leaf (.eqSym 6 19 6 (-46343769407)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 6 20 6 (-71151124780))) (.leaf (.eqSym 7 8 1 (-128884732473)))) (.node (.leaf (.eqSym 7 8 2 1275494171431)) (.leaf (.eqSym 7 8 7 53125630149))))
            (.node (.node (.leaf (.eqSym 7 9 0 (-435827060440))) (.leaf (.eqSym 7 9 4 (-3354465268798)))) (.node (.leaf (.eqSym 7 9 6 (-2710011469039))) (.leaf (.eqSym 7 9 7 745977910303)))))
            (.node
            (.node (.node (.leaf (.eqSym 7 10 0 1188114753019)) (.leaf (.eqSym 7 10 2 (-1776374629042)))) (.node (.leaf (.eqSym 7 10 3 (-1334386111923))) (.leaf (.eqSym 7 10 4 2947248395666))))
            (.node (.node (.leaf (.eqSym 7 10 6 2638128680630)) (.leaf (.eqSym 7 10 7 (-725155863314)))) (.node (.leaf (.eqSym 7 11 0 (-859379775823))) (.leaf (.eqSym 7 11 7 226671538577)))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 7 12 6 125564773455)) (.leaf (.eqSym 7 13 1 314203305945))) (.node (.leaf (.eqSym 7 13 3 2502396332532)) (.leaf (.eqSym 7 14 0 52011979815))))
            (.node (.node (.leaf (.eqSym 7 14 3 (-652767928549))) (.leaf (.eqSym 7 14 7 (-116965942954)))) (.node (.leaf (.eqSym 7 15 1 (-31093491449))) (.leaf (.eqSym 7 15 7 36991087905)))))
            (.node
            (.node (.node (.leaf (.eqSym 7 16 3 (-308669082928))) (.leaf (.eqSym 7 17 3 24757131660))) (.node (.leaf (.eqSym 7 17 4 (-251951031368))) (.leaf (.eqSym 7 17 5 (-1076132113235)))))
            (.node (.node (.leaf (.eqSym 7 17 6 915334495535)) (.leaf (.eqSym 7 17 7 (-1892702628021)))) (.node (.leaf (.eqSym 7 18 5 848747273019)) (.leaf (.eqSym 7 18 6 (-2763478740310)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 7 18 7 2317934316449)) (.leaf (.eqSym 7 19 6 1627502107192))) (.node (.leaf (.eqSym 7 19 7 (-104838339308))) (.leaf (.eqSym 8 9 2 (-1517205984810)))))
            (.node (.node (.leaf (.eqSym 8 9 4 2789247092494)) (.leaf (.eqSym 8 9 6 (-118133421329)))) (.node (.leaf (.eqSym 8 10 0 (-934855664464))) (.leaf (.eqSym 8 10 2 2533618136086)))))
            (.node
            (.node (.node (.leaf (.eqSym 8 10 8 1248704940644)) (.leaf (.eqSym 8 11 0 653836410691))) (.node (.leaf (.eqSym 8 11 3 4778129862593)) (.leaf (.eqSym 8 11 4 (-3897569452337)))))
            (.node (.node (.leaf (.eqSym 8 11 7 224116279146)) (.leaf (.eqSym 8 11 8 (-1298545881232)))) (.node (.leaf (.eqSym 8 12 1 544415123431)) (.leaf (.eqSym 8 12 3 (-2016265946652)))))))))))
      (.node
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 8 12 6 134643380628)) (.node (.leaf (.eqSym 8 13 1 (-549861798601))) (.leaf (.eqSym 8 13 3 (-2397884265059)))))
            (.node (.node (.leaf (.eqSym 8 13 4 449624483067)) (.leaf (.eqSym 8 14 2 278697622467))) (.node (.leaf (.eqSym 8 14 7 (-264538790231))) (.leaf (.eqSym 8 16 4 578115274439)))))
            (.node
            (.node (.node (.leaf (.eqSym 8 16 5 873313510116)) (.leaf (.eqSym 8 16 8 543590948999))) (.node (.leaf (.eqSym 8 19 6 (-631975454917))) (.leaf (.eqSym 8 19 7 (-24703187258)))))
            (.node (.node (.leaf (.eqSym 8 19 8 (-562607445228))) (.leaf (.eqSym 8 20 7 328810579390))) (.node (.leaf (.eqSym 8 20 8 230855946903)) (.leaf (.eqSym 9 10 0 292031464910))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 9 10 1 (-2169988189659))) (.leaf (.eqSym 9 10 7 (-3044338661141)))) (.node (.leaf (.eqSym 9 10 9 (-1325478646350))) (.leaf (.eqSym 9 11 0 (-271856567906)))))
            (.node (.node (.leaf (.eqSym 9 11 1 2220811049749)) (.leaf (.eqSym 9 11 8 1786314495928))) (.node (.leaf (.eqSym 9 11 9 532075972257)) (.leaf (.eqSym 9 12 1 (-759216045443))))))
            (.node
            (.node (.node (.leaf (.eqSym 9 12 6 45604750998)) (.leaf (.eqSym 9 12 9 (-18082926964)))) (.node (.leaf (.eqSym 9 13 1 157851359631)) (.leaf (.eqSym 9 13 4 (-878393622044)))))
            (.node (.node (.leaf (.eqSym 9 14 7 453209590962)) (.leaf (.eqSym 9 15 5 438375798469))) (.node (.leaf (.eqSym 9 16 8 347672298271)) (.leaf (.eqSym 9 18 7 984098060509)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 9 18 8 389934177461)) (.node (.leaf (.eqSym 9 18 9 (-1571631075346))) (.leaf (.eqSym 9 19 7 (-451547051651)))))
            (.node (.node (.leaf (.eqSym 9 19 8 (-2017617991619))) (.leaf (.eqSym 9 19 9 1852088393470))) (.node (.leaf (.eqSym 9 20 8 699544799294)) (.leaf (.eqSym 9 20 9 (-305715936203))))))
            (.node
            (.node (.node (.leaf (.eqSym 10 11 0 (-98916182177))) (.leaf (.eqSym 10 11 2 (-3232468376898)))) (.node (.leaf (.eqSym 10 11 7 1306561219497)) (.leaf (.eqSym 10 11 9 (-1711780393867)))))
            (.node (.node (.leaf (.eqSym 10 11 10 774356519653)) (.leaf (.eqSym 10 12 1 243846721222))) (.node (.leaf (.eqSym 10 12 3 2492861584236)) (.leaf (.eqSym 10 12 6 2078839767118))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 10 12 7 (-2601649823770))) (.leaf (.eqSym 10 13 3 (-3004614093)))) (.node (.leaf (.eqSym 10 13 8 373955164998)) (.leaf (.eqSym 10 13 9 (-213730732397)))))
            (.node (.node (.leaf (.eqSym 10 14 7 (-857995477517))) (.leaf (.eqSym 10 15 7 (-457257166018)))) (.node (.leaf (.eqSym 10 15 8 (-158242241113))) (.leaf (.eqSym 10 16 6 (-835072702418))))))
            (.node
            (.node (.node (.leaf (.eqSym 10 16 10 (-291610730325))) (.leaf (.eqSym 10 17 8 364055591226))) (.node (.leaf (.eqSym 10 17 9 950601485832)) (.leaf (.eqSym 10 17 10 2426141792549))))
            (.node (.node (.leaf (.eqSym 10 18 7 83579884809)) (.leaf (.eqSym 10 18 10 (-2930019691821)))) (.node (.leaf (.eqSym 10 19 8 826039441900)) (.leaf (.eqSym 10 19 9 411285358961))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 10 20 9 (-1246656065158))) (.node (.leaf (.eqSym 10 20 10 2165004384675)) (.leaf (.eqSym 11 12 3 (-861763188037)))))
            (.node (.node (.leaf (.eqSym 11 12 4 (-907216087959))) (.leaf (.eqSym 11 12 6 (-66362056191)))) (.node (.leaf (.eqSym 11 12 9 1109387714091)) (.leaf (.eqSym 11 12 11 (-154473083572))))))
            (.node
            (.node (.node (.leaf (.eqSym 11 13 4 1137247443459)) (.leaf (.eqSym 11 13 10 (-339455884896)))) (.node (.leaf (.eqSym 11 14 4 (-445563411310))) (.leaf (.eqSym 11 14 7 650179677424))))
            (.node (.node (.leaf (.eqSym 11 14 9 207816258435)) (.leaf (.eqSym 11 14 11 75052693970))) (.node (.leaf (.eqSym 11 15 5 127872835000)) (.leaf (.eqSym 11 15 8 592134579323))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 11 15 11 (-47894517394))) (.leaf (.eqSym 11 16 6 43784951982))) (.node (.leaf (.eqSym 11 16 8 (-771780251024))) (.leaf (.eqSym 11 16 10 (-293892407700)))))
            (.node (.node (.leaf (.eqSym 11 17 7 (-15915298924))) (.leaf (.eqSym 11 17 8 166544549299))) (.node (.leaf (.eqSym 11 17 10 (-1391946720493))) (.leaf (.eqSym 11 17 11 (-1349408327909))))))
            (.node
            (.node (.node (.leaf (.eqSym 11 18 9 (-910270319968))) (.leaf (.eqSym 11 18 10 824706008066))) (.node (.leaf (.eqSym 11 18 11 2763307762822)) (.leaf (.eqSym 11 19 9 58220336216))))
            (.node (.node (.leaf (.eqSym 11 19 10 896993251188)) (.leaf (.eqSym 11 19 11 (-786925886336)))) (.node (.leaf (.eqSym 11 20 10 111146581606)) (.leaf (.eqSym 11 20 11 (-2078584934855))))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 11 21 11 122864036775)) (.leaf (.eqSym 12 13 4 (-101023307913)))) (.node (.leaf (.eqSym 12 13 9 (-566240566290))) (.leaf (.eqSym 12 13 10 796493911009))))
            (.node (.node (.leaf (.eqSym 12 13 12 44597088974)) (.leaf (.eqSym 12 15 7 (-330017238624)))) (.node (.leaf (.eqSym 12 16 8 537963572740)) (.leaf (.eqSym 12 17 11 (-1391175255231))))))
            (.node
            (.node (.node (.leaf (.eqSym 12 18 9 (-165835164845))) (.leaf (.eqSym 12 18 11 2671354709148))) (.node (.leaf (.eqSym 12 19 11 (-1925279829835))) (.leaf (.eqSym 12 20 11 517116697534))))
            (.node (.node (.leaf (.eqSym 13 14 6 691829009529)) (.leaf (.eqSym 13 14 7 (-201356913938)))) (.node (.leaf (.eqSym 13 15 7 (-392900462476))) (.leaf (.eqSym 13 15 10 40538507677))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 13 16 8 25724720090)) (.leaf (.eqSym 13 16 9 63293632071))) (.node (.leaf (.eqSym 13 16 13 (-31758920129))) (.leaf (.eqSym 13 17 12 1296418686780))))
            (.node (.node (.leaf (.eqSym 13 18 12 (-2510768905419))) (.leaf (.eqSym 13 19 12 1725637365705))) (.node (.leaf (.eqSym 13 19 13 8700852485)) (.leaf (.eqSym 13 20 12 (-418776785781))))))
            (.node
            (.node (.node (.leaf (.eqSym 14 15 8 336601229803)) (.leaf (.eqSym 14 15 11 15024873025))) (.node (.leaf (.eqSym 14 15 13 192825982276)) (.leaf (.eqSym 14 15 14 (-48746060930)))))
            (.node (.node (.leaf (.eqSym 14 17 14 (-155986845234))) (.leaf (.eqSym 14 18 14 105863453617))) (.node (.leaf (.eqSym 14 20 13 (-6844352898089))) (.leaf (.eqSym 14 20 14 (-39983677356))))))))))
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 14 21 14 90594712315)) (.node (.leaf (.eqSym 15 16 10 (-112701534013))) (.leaf (.eqSym 15 16 12 323842022733))))
            (.node (.node (.leaf (.eqSym 15 16 14 41384936895)) (.leaf (.eqSym 15 16 15 125931815856))) (.node (.leaf (.eqSym 15 17 14 256829275737)) (.leaf (.eqSym 15 18 14 (-16344057732))))))
            (.node
            (.node (.node (.leaf (.eqSym 15 18 15 (-286875949476))) (.leaf (.eqSym 15 19 14 (-799287995956)))) (.node (.leaf (.eqSym 15 20 14 14490887607932)) (.leaf (.eqSym 15 20 15 553740040622))))
            (.node (.node (.leaf (.eqSym 15 21 15 (-280927633484))) (.leaf (.eqSym 16 19 14 (-136826987312)))) (.node (.leaf (.eqSym 16 19 15 335965862297)) (.leaf (.eqSym 16 19 16 61715689978))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 16 20 15 (-8144354275483))) (.leaf (.eqSym 16 20 16 (-232652257403)))) (.node (.leaf (.eqSym 17 18 15 114623341584)) (.leaf (.eqSym 17 18 16 108012571706))))
            (.node (.node (.leaf (.eqSym 17 18 17 121550504776)) (.leaf (.eqSym 17 19 15 (-2475713166)))) (.node (.leaf (.eqSym 17 19 16 (-74032580618))) (.leaf (.eqSym 17 19 17 (-80038639909))))))
            (.node
            (.node (.node (.leaf (.eqSym 18 19 17 254020990833)) (.leaf (.eqSym 18 19 18 10384351786))) (.node (.leaf (.eqSym 18 20 17 (-242550128689))) (.leaf (.eqSym 18 20 18 (-188863303156)))))
            (.node (.node (.leaf (.eqSym 18 21 18 401713556369)) (.leaf (.eqSym 19 20 18 885701250104))) (.node (.leaf (.eqSym 19 20 19 303474343127)) (.leaf (.eqSym 19 21 19 (-376343255957))))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 20 21 20 106850718636)) (.node (.leaf (.eqPFix 2 1 3645535042469)) (.leaf (.eqPFix 20 1 17350067450859))))
            (.node (.node (.leaf (.eqPFix 21 0 (-593322416827))) (.leaf (.ubHLePi 0 0 0 547700205782))) (.node (.leaf (.ubHLePj 0 0 1 78046672141)) (.leaf (.ubHLePi 1 1 0 89597355345)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 2 0 2 144950055910)) (.leaf (.ubHMcc 2 0 7 182430549615))) (.node (.leaf (.ubHLePi 2 0 9 144621424159)) (.leaf (.ubHMcc 2 0 18 54389298630))))
            (.node (.node (.leaf (.ubHLePi 2 0 19 55855229568)) (.leaf (.ubHMcc 2 1 4 431340588730))) (.node (.leaf (.ubHLePi 2 1 5 449908452323)) (.leaf (.ubHMcc 2 1 14 273718658372))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 2 1 16 309780674833)) (.leaf (.ubHLePi 2 2 1 102746590084))) (.node (.leaf (.ubHMcc 2 2 4 46060551577)) (.leaf (.ubHLePi 3 0 18 446400109))))
            (.node (.node (.leaf (.ubHGe0 4 0 0 1059327375909)) (.leaf (.ubHLePj 4 0 1 1792987336024))) (.node (.leaf (.ubHLePj 4 1 0 1065644403112)) (.leaf (.ubHGe0 5 0 0 443726310240)))))
            (.node
            (.node (.node (.leaf (.ubHLePj 5 0 1 755798133990)) (.leaf (.ubHGe0 5 0 5 274197376))) (.node (.leaf (.ubHGe0 5 0 14 372027243)) (.leaf (.ubHGe0 5 3 2 199340702))))
            (.node (.node (.leaf (.ubHLePi 5 5 0 46417035836)) (.leaf (.ubHLePj 5 5 15 405984943223))) (.node (.leaf (.ubHLePj 6 0 1 135937188843)) (.leaf (.ubHLePj 6 0 12 395072776))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 6 6 0 86371305073)) (.node (.leaf (.ubHLePj 6 6 13 107356445281)) (.leaf (.ubHLePi 7 0 14 112806374))))
            (.node (.node (.leaf (.ubHGe0 7 5 0 368949934)) (.leaf (.ubHLePj 7 7 1 970768053))) (.node (.leaf (.ubHGe0 7 7 14 383299177718)) (.leaf (.ubHGe0 9 0 0 1367407697377)))))
            (.node
            (.node (.node (.leaf (.ubHLePj 9 0 1 1463352103473)) (.leaf (.ubHMcc 9 0 10 89915760))) (.node (.leaf (.ubHLePj 9 1 0 1908671322135)) (.leaf (.ubHLePi 9 9 0 632703763364))))
            (.node (.node (.leaf (.ubHMcc 9 9 2 662453233)) (.leaf (.ubHMcc 10 1 9 65594785))) (.node (.leaf (.ubHLePi 10 5 1 387605298)) (.leaf (.ubHLePi 10 5 10 333825055))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHMcc 10 9 2 479471900)) (.leaf (.ubHMcc 10 10 10 1490671859279))) (.node (.leaf (.ubHLePi 10 10 11 158586670789)) (.leaf (.ubHGe0 11 0 0 216973686317))))
            (.node (.node (.leaf (.ubHLePj 11 0 1 948764523184)) (.leaf (.ubHMcc 11 2 10 85633035))) (.node (.leaf (.ubHMcc 11 5 5 152723324)) (.leaf (.ubHLePi 11 10 5 465123571)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 11 11 0 360058362279)) (.leaf (.ubHLePj 11 11 9 1283605485621))) (.node (.leaf (.ubHLePj 13 1 0 395447003145)) (.leaf (.ubHLePi 13 13 0 14719152723))))
            (.node (.node (.leaf (.ubHGe0 14 0 0 88230671796)) (.leaf (.ubHLePj 14 1 0 230682975451))) (.node (.leaf (.ubHLePj 14 13 0 1845922614)) (.leaf (.ubHLePj 14 13 7 6715434534006)))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 14 14 0 28817563322)) (.leaf (.ubHGe0 14 14 2 6779238128))) (.node (.leaf (.ubHGe0 15 0 0 204025984133)) (.leaf (.ubHLePj 15 0 1 107413581629))))
            (.node (.node (.leaf (.ubHLePj 15 1 0 44838164044)) (.leaf (.ubHLePj 15 3 6 502705131))) (.node (.leaf (.ubHLePj 15 12 0 1975940276)) (.leaf (.ubHLePj 15 13 6 70579689284)))))
            (.node
            (.node (.node (.leaf (.ubHMcc 15 14 6 14127860723971)) (.leaf (.ubHGe0 16 2 5 652184658))) (.node (.leaf (.ubHGe0 16 11 5 1337641785)) (.leaf (.ubHLePj 16 15 5 8228458806340))))
            (.node (.node (.leaf (.ubHLePi 16 16 0 69211758970)) (.leaf (.ubHLePi 17 16 0 7050235513))) (.node (.leaf (.ubHGe0 18 0 0 983181712984)) (.leaf (.ubHLePj 18 0 1 1016130410645))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePj 18 1 0 1449249524268)) (.leaf (.ubHLePi 18 18 0 54061509739))) (.node (.leaf (.ubHGe0 18 18 3 213074794568)) (.leaf (.ubHLePj 19 1 0 654499077668))))
            (.node (.node (.leaf (.ubHMcc 19 1 2 21008993243)) (.leaf (.ubHMcc 19 9 1 64849464515))) (.node (.leaf (.ubHMcc 19 11 0 72582213703)) (.leaf (.ubHLePi 19 15 1 164693314959)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 19 16 0 39366564412)) (.leaf (.ubHMcc 19 17 2 568048213769))) (.node (.leaf (.ubHMcc 19 18 1 301543087301)) (.leaf (.ubHLePj 20 1 1 2248704396377))))
            (.node (.node (.leaf (.ubHMcc 20 2 1 1550778259812)) (.leaf (.ubHLePi 20 20 0 131352136441))) (.node (.leaf (.ubHLePj 21 1 0 155343847125)) (.leaf (.ubHLePj 21 5 0 343255142458)))))))))))
    (.node
      (.node
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 21 21 0 5727100741)) (.node (.leaf (.ubHLePi 0 0 6 23117)) (.leaf (.ubHGe0 0 0 5 130078))))
            (.node (.node (.leaf (.ubHLePi 0 0 4 306159)) (.leaf (.ubHGe0 0 0 3 385630))) (.node (.leaf (.ubHLePi 0 0 2 274055)) (.leaf (.ubHGe0 0 0 1 104157)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 1 0 6 10116)) (.leaf (.ubHGe0 1 1 5 3804))) (.node (.leaf (.ubHLePi 1 0 5 60696)) (.leaf (.ubHLePi 1 1 4 17900))))
            (.node (.node (.leaf (.ubHGe0 1 0 4 151740)) (.leaf (.ubHGe0 1 1 3 33813))) (.node (.leaf (.ubHLePi 1 0 3 202320)) (.leaf (.ubHLePi 1 1 2 32037))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 1 0 2 151740)) (.leaf (.ubHGe0 1 1 1 15219))) (.node (.leaf (.ubHLePi 1 0 1 60696)) (.leaf (.ubHGe0 1 0 0 10116))))
            (.node (.node (.leaf (.ubHLePi 2 0 6 2695)) (.leaf (.ubHLePi 2 2 4 258))) (.node (.leaf (.ubHGe0 2 0 5 19863)) (.leaf (.ubHGe0 2 1 4 23031)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 2 2 3 903)) (.leaf (.ubHLePi 2 0 4 57568))) (.node (.leaf (.ubHLePi 2 1 3 43506)) (.leaf (.ubHLePi 2 2 2 1196))))
            (.node (.node (.leaf (.ubHGe0 2 0 3 85910)) (.leaf (.ubHGe0 2 1 2 41217))) (.node (.leaf (.ubHGe0 2 2 1 711)) (.leaf (.ubHLePi 2 1 1 19580)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 2 2 0 160)) (.node (.leaf (.ubHGe0 2 0 1 30316)) (.leaf (.ubHGe0 2 1 0 3731))))
            (.node (.node (.leaf (.ubHLePi 2 0 0 5370)) (.leaf (.ubHLePi 3 0 6 9692))) (.node (.leaf (.ubHLePi 3 1 5 24286)) (.leaf (.ubHLePi 3 2 4 6930)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 3 3 3 525)) (.leaf (.ubHGe0 3 0 5 77526))) (.node (.leaf (.ubHGe0 3 1 4 126188)) (.leaf (.ubHGe0 3 2 3 27389))))
            (.node (.node (.leaf (.ubHGe0 3 3 2 1470)) (.leaf (.ubHLePi 3 0 4 241980))) (.node (.leaf (.ubHLePi 3 1 3 262246)) (.leaf (.ubHLePi 3 2 2 40657))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 3 3 1 1380)) (.leaf (.ubHGe0 3 0 3 387165))) (.node (.leaf (.ubHGe0 3 1 2 272385)) (.leaf (.ubHGe0 3 2 1 26858))))
            (.node (.node (.leaf (.ubHGe0 3 3 0 434)) (.leaf (.ubHLePi 3 0 2 339344))) (.node (.leaf (.ubHLePi 3 1 1 141367)) (.leaf (.ubHLePi 3 2 0 6660)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 3 0 1 155659)) (.leaf (.ubHGe0 3 1 0 29325))) (.node (.leaf (.ubHLePi 3 0 0 29332)) (.leaf (.ubHLePi 4 0 6 5158))))
            (.node (.node (.leaf (.ubHLePi 4 1 5 2372)) (.leaf (.ubHGe0 4 2 4 74))) (.node (.leaf (.ubHLePi 4 3 3 16)) (.leaf (.ubHLePi 4 4 2 9))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHGe0 4 0 5 30853)) (.node (.leaf (.ubHGe0 4 1 4 10839)) (.leaf (.ubHLePi 4 2 3 284))))
            (.node (.node (.leaf (.ubHGe0 4 3 2 48)) (.leaf (.ubHGe0 4 4 1 14))) (.node (.leaf (.ubHLePi 4 0 4 76858)) (.leaf (.ubHLePi 4 1 3 19896)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 4 2 2 412)) (.leaf (.ubHLePi 4 3 1 48))) (.node (.leaf (.ubHLePi 4 4 0 6)) (.leaf (.ubHGe0 4 0 3 102073))))
            (.node (.node (.leaf (.ubHGe0 4 1 2 18312)) (.leaf (.ubHLePi 4 2 1 267))) (.node (.leaf (.ubHGe0 4 3 0 16)) (.leaf (.ubHLePi 4 0 2 76217))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 4 1 1 8443)) (.leaf (.ubHGe0 4 2 0 65))) (.node (.leaf (.ubHGe0 4 0 1 30335)) (.leaf (.ubHGe0 4 1 0 1559))))
            (.node (.node (.leaf (.ubHLePi 4 0 0 5027)) (.leaf (.ubHGe0 5 0 6 2866))) (.node (.leaf (.ubHGe0 5 1 5 947)) (.leaf (.ubHLePi 5 2 4 884)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 5 3 3 607)) (.leaf (.ubHLePi 5 4 2 109))) (.node (.leaf (.ubHLePi 5 5 1 3)) (.leaf (.ubHLePi 5 0 5 16513))))
            (.node (.node (.leaf (.ubHLePi 5 1 4 2876)) (.leaf (.ubHGe0 5 2 3 4716))) (.node (.leaf (.ubHGe0 5 4 1 219)) (.leaf (.ubHGe0 5 5 0 3)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHGe0 5 0 4 39242)) (.node (.leaf (.ubHGe0 5 1 3 1370)) (.leaf (.ubHLePi 5 2 2 9034))))
            (.node (.node (.leaf (.ubHLePi 5 3 1 2240)) (.leaf (.ubHLePi 5 4 0 110))) (.node (.leaf (.ubHLePi 5 0 3 48909)) (.leaf (.ubHGe0 5 1 2 3803)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 5 2 1 7464)) (.leaf (.ubHGe0 5 3 0 818))) (.node (.leaf (.ubHGe0 5 0 2 33396)) (.leaf (.ubHLePi 5 1 1 4950))))
            (.node (.node (.leaf (.ubHLePi 5 2 0 2262)) (.leaf (.ubHLePi 5 0 1 11665))) (.node (.leaf (.ubHGe0 5 1 0 1706)) (.leaf (.ubHGe0 6 0 6 1664))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 6 1 5 7059)) (.leaf (.ubHGe0 6 2 4 7538))) (.node (.leaf (.ubHGe0 6 3 3 3140)) (.leaf (.ubHGe0 6 4 2 511))))
            (.node (.node (.leaf (.ubHGe0 6 5 1 19)) (.leaf (.ubHLePi 6 0 5 15921))) (.node (.leaf (.ubHLePi 6 1 4 47021)) (.leaf (.ubHLePi 6 2 3 37049)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 6 3 2 10805)) (.leaf (.ubHLePi 6 4 1 1073))) (.node (.leaf (.ubHLePi 6 5 0 19)) (.leaf (.ubHGe0 6 0 4 59394))))
            (.node (.node (.leaf (.ubHGe0 6 1 3 122963)) (.leaf (.ubHGe0 6 2 2 67508))) (.node (.leaf (.ubHGe0 6 3 1 12256)) (.leaf (.ubHGe0 6 4 0 562)))))))))
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 6 0 3 113166)) (.node (.leaf (.ubHLePi 6 1 2 158213)) (.leaf (.ubHLePi 6 2 1 54072))))
            (.node (.node (.leaf (.ubHLePi 6 3 0 4592)) (.leaf (.ubHGe0 6 0 2 117567))) (.node (.leaf (.ubHGe0 6 1 1 100349)) (.leaf (.ubHGe0 6 2 0 16075)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 6 0 1 63594)) (.leaf (.ubHLePi 6 1 0 25136))) (.node (.leaf (.ubHGe0 6 0 0 14056)) (.leaf (.ubHLePi 7 0 6 2456))))
            (.node (.node (.leaf (.ubHLePi 7 1 5 7005)) (.leaf (.ubHLePi 7 2 4 8416))) (.node (.leaf (.ubHLePi 7 3 3 4464)) (.leaf (.ubHLePi 7 4 2 944))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 7 5 1 52)) (.leaf (.ubHLePi 7 6 0 3))) (.node (.leaf (.ubHGe0 7 0 5 19930)) (.leaf (.ubHGe0 7 1 4 47496))))
            (.node (.node (.leaf (.ubHGe0 7 2 3 43232)) (.leaf (.ubHGe0 7 3 2 15858))) (.node (.leaf (.ubHGe0 7 4 1 2010)) (.leaf (.ubHLePi 7 0 4 67867)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 7 1 3 127609)) (.leaf (.ubHLePi 7 2 2 82048))) (.node (.leaf (.ubHLePi 7 3 1 18490)) (.leaf (.ubHLePi 7 4 0 1079))))
            (.node (.node (.leaf (.ubHGe0 7 0 3 123457)) (.leaf (.ubHGe0 7 1 2 169413))) (.node (.leaf (.ubHGe0 7 2 1 68176)) (.leaf (.ubHGe0 7 3 0 7109)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 7 0 2 125924)) (.node (.leaf (.ubHLePi 7 1 1 111003)) (.leaf (.ubHLePi 7 2 0 20953))))
            (.node (.node (.leaf (.ubHGe0 7 0 1 68043)) (.leaf (.ubHGe0 7 1 0 28711))) (.node (.leaf (.ubHLePi 7 0 0 15183)) (.leaf (.ubHLePi 8 0 6 443)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 8 1 5 3206)) (.leaf (.ubHLePi 8 2 4 6488))) (.node (.leaf (.ubHLePi 8 3 3 5728)) (.leaf (.ubHLePi 8 4 2 2191))))
            (.node (.node (.leaf (.ubHLePi 8 5 1 296)) (.leaf (.ubHLePi 8 6 0 8))) (.node (.leaf (.ubHGe0 8 0 5 5509)) (.leaf (.ubHGe0 8 1 4 26670))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 8 2 3 39609)) (.leaf (.ubHGe0 8 3 2 23817))) (.node (.leaf (.ubHGe0 8 4 1 5413)) (.leaf (.ubHGe0 8 5 0 326))))
            (.node (.node (.leaf (.ubHLePi 8 0 4 25296)) (.leaf (.ubHLePi 8 1 3 86049))) (.node (.leaf (.ubHLePi 8 2 2 87992)) (.leaf (.ubHLePi 8 3 1 32070)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 8 4 0 3281)) (.leaf (.ubHGe0 8 0 3 58306))) (.node (.leaf (.ubHGe0 8 1 2 134723)) (.leaf (.ubHGe0 8 2 1 84442))))
            (.node (.node (.leaf (.ubHGe0 8 3 0 14045)) (.leaf (.ubHLePi 8 0 2 72542))) (.node (.leaf (.ubHLePi 8 1 1 102522)) (.leaf (.ubHLePi 8 2 0 29611))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHGe0 8 0 1 46568)) (.node (.leaf (.ubHGe0 8 1 0 30397)) (.leaf (.ubHLePi 8 0 0 12103))))
            (.node (.node (.leaf (.ubHLePi 9 0 6 116)) (.leaf (.ubHLePi 9 1 5 3146))) (.node (.leaf (.ubHLePi 9 2 4 7109)) (.leaf (.ubHLePi 9 3 3 6274)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 9 4 2 2258)) (.leaf (.ubHLePi 9 5 1 233))) (.node (.leaf (.ubHLePi 9 6 0 7)) (.leaf (.ubHGe0 9 0 5 3749))))
            (.node (.node (.leaf (.ubHGe0 9 1 4 27888)) (.leaf (.ubHGe0 9 2 3 43818))) (.node (.leaf (.ubHGe0 9 3 2 25728)) (.leaf (.ubHGe0 9 4 1 5257))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 9 5 0 248)) (.leaf (.ubHLePi 9 0 4 22107))) (.node (.leaf (.ubHLePi 9 1 3 93002)) (.leaf (.ubHLePi 9 2 2 97102))))
            (.node (.node (.leaf (.ubHLePi 9 3 1 33668)) (.leaf (.ubHLePi 9 4 0 3009))) (.node (.leaf (.ubHGe0 9 0 3 57043)) (.leaf (.ubHGe0 9 1 2 147755)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 9 2 1 91968)) (.leaf (.ubHGe0 9 3 0 14214))) (.node (.leaf (.ubHLePi 9 0 2 75198)) (.leaf (.ubHLePi 9 1 1 112633))))
            (.node (.node (.leaf (.ubHLePi 9 2 0 31569)) (.leaf (.ubHGe0 9 0 1 49702))) (.node (.leaf (.ubHGe0 9 1 0 33134)) (.leaf (.ubHLePi 9 0 0 13071)))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 10 0 6 331)) (.leaf (.ubHGe0 10 1 5 3857))) (.node (.leaf (.ubHGe0 10 2 4 8787)) (.leaf (.ubHGe0 10 3 3 7262))))
            (.node (.node (.leaf (.ubHGe0 10 4 2 1744)) (.leaf (.ubHLePi 10 6 0 248))) (.node (.leaf (.ubHLePi 10 0 5 5519)) (.leaf (.ubHLePi 10 1 4 34219)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 10 2 3 53148)) (.leaf (.ubHLePi 10 3 2 27164))) (.node (.leaf (.ubHLePi 10 4 1 1550)) (.leaf (.ubHGe0 10 5 0 1600))))
            (.node (.node (.leaf (.ubHGe0 10 0 4 28998)) (.leaf (.ubHGe0 10 1 3 113742))) (.node (.leaf (.ubHGe0 10 2 2 113321)) (.leaf (.ubHGe0 10 3 1 29096))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 10 4 0 2587)) (.leaf (.ubHLePi 10 0 3 72019))) (.node (.leaf (.ubHLePi 10 1 2 178180)) (.leaf (.ubHLePi 10 2 1 99243))))
            (.node (.node (.leaf (.ubHLePi 10 3 0 6479)) (.leaf (.ubHGe0 10 0 2 93053))) (.node (.leaf (.ubHGe0 10 1 1 131322)) (.leaf (.ubHGe0 10 2 0 28512)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 10 0 1 60186)) (.leaf (.ubHLePi 10 1 0 35894))) (.node (.leaf (.ubHGe0 10 0 0 15247)) (.leaf (.ubHLePi 11 0 6 5))))
            (.node (.node (.leaf (.ubHGe0 11 1 5 822)) (.leaf (.ubHGe0 11 2 4 3041))) (.node (.leaf (.ubHGe0 11 3 3 4115)) (.leaf (.ubHGe0 11 4 2 3024))))))))))
      (.node
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHGe0 11 5 1 1021)) (.node (.leaf (.ubHGe0 11 6 0 215)) (.leaf (.ubHLePi 11 0 5 838))))
            (.node (.node (.leaf (.ubHLePi 11 1 4 9591)) (.leaf (.ubHLePi 11 2 3 22792))) (.node (.leaf (.ubHLePi 11 3 2 22652)) (.leaf (.ubHLePi 11 4 1 10315)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 11 5 0 2043)) (.leaf (.ubHGe0 11 0 4 6630))) (.node (.leaf (.ubHGe0 11 1 3 39391)) (.leaf (.ubHGe0 11 2 2 63653))))
            (.node (.node (.leaf (.ubHGe0 11 3 1 40338)) (.leaf (.ubHGe0 11 4 0 9410))) (.node (.leaf (.ubHLePi 11 0 3 20835)) (.leaf (.ubHLePi 11 1 2 76910))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 11 2 1 77607)) (.leaf (.ubHLePi 11 3 0 24214))) (.node (.leaf (.ubHGe0 11 0 2 32978)) (.leaf (.ubHGe0 11 1 1 72812))))
            (.node (.node (.leaf (.ubHGe0 11 2 0 35285)) (.leaf (.ubHLePi 11 0 1 26285))) (.node (.leaf (.ubHLePi 11 1 0 27085)) (.leaf (.ubHLePi 12 0 6 13)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 12 1 5 225)) (.leaf (.ubHLePi 12 2 4 558))) (.node (.leaf (.ubHLePi 12 3 3 725)) (.leaf (.ubHLePi 12 4 2 545))))
            (.node (.node (.leaf (.ubHGe0 12 5 1 268)) (.leaf (.ubHGe0 12 6 0 340))) (.node (.leaf (.ubHGe0 12 0 5 274)) (.leaf (.ubHGe0 12 1 4 1957)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHGe0 12 2 3 3975)) (.node (.leaf (.ubHGe0 12 3 2 4141)) (.leaf (.ubHGe0 12 4 1 4))))
            (.node (.node (.leaf (.ubHLePi 12 5 0 1994)) (.leaf (.ubHLePi 12 0 4 1489))) (.node (.leaf (.ubHLePi 12 1 3 7099)) (.leaf (.ubHLePi 12 2 2 11334)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 12 3 1 4274)) (.leaf (.ubHGe0 12 4 0 4290))) (.node (.leaf (.ubHGe0 12 0 3 3947)) (.leaf (.ubHGe0 12 1 2 13527))))
            (.node (.node (.leaf (.ubHGe0 12 2 1 11372)) (.leaf (.ubHLePi 12 3 0 3564))) (.node (.leaf (.ubHLePi 12 0 2 5850)) (.leaf (.ubHLePi 12 1 1 11743))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 12 2 0 482)) (.leaf (.ubHGe0 12 0 1 4394))) (.node (.leaf (.ubHGe0 12 1 0 2505)) (.leaf (.ubHLePi 12 0 0 1099))))
            (.node (.node (.leaf (.ubHGe0 13 0 6 17)) (.leaf (.ubHGe0 13 1 5 445))) (.node (.leaf (.ubHGe0 13 2 4 2897)) (.leaf (.ubHGe0 13 3 3 8153)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 13 4 2 10753)) (.leaf (.ubHGe0 13 5 1 6539))) (.node (.leaf (.ubHGe0 13 6 0 1379)) (.leaf (.ubHLePi 13 0 5 509))))
            (.node (.node (.leaf (.ubHLePi 13 1 4 7416)) (.leaf (.ubHLePi 13 2 3 33430))) (.node (.leaf (.ubHLePi 13 3 2 62558)) (.leaf (.ubHLePi 13 4 1 50182))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 13 5 0 13768)) (.node (.leaf (.ubHGe0 13 0 4 4637)) (.leaf (.ubHGe0 13 1 3 44982))))
            (.node (.node (.leaf (.ubHGe0 13 2 2 134249)) (.leaf (.ubHGe0 13 3 1 151757))) (.node (.leaf (.ubHGe0 13 4 0 55475)) (.leaf (.ubHLePi 13 0 3 19828)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 13 1 2 125975)) (.leaf (.ubHLePi 13 2 1 225877))) (.node (.leaf (.ubHLePi 13 3 0 116586)) (.leaf (.ubHGe0 13 0 2 43608))))
            (.node (.node (.leaf (.ubHGe0 13 1 1 165428)) (.leaf (.ubHGe0 13 2 0 135263))) (.node (.leaf (.ubHLePi 13 0 1 47691)) (.leaf (.ubHLePi 13 1 0 82263))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 13 0 0 20504)) (.leaf (.ubHGe0 14 0 6 7))) (.node (.leaf (.ubHGe0 14 1 5 129)) (.leaf (.ubHGe0 14 2 4 869))))
            (.node (.node (.leaf (.ubHGe0 14 3 3 2161)) (.leaf (.ubHGe0 14 4 2 1242))) (.node (.leaf (.ubHLePi 14 5 1 2297)) (.leaf (.ubHLePi 14 6 0 767)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 14 0 5 150)) (.leaf (.ubHLePi 14 1 4 2178))) (.node (.leaf (.ubHLePi 14 2 3 9168)) (.leaf (.ubHLePi 14 3 2 10636))))
            (.node (.node (.leaf (.ubHGe0 14 4 1 8040)) (.leaf (.ubHGe0 14 5 0 6448))) (.node (.leaf (.ubHGe0 14 0 4 1344)) (.leaf (.ubHGe0 14 1 3 12513)))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 14 2 2 27649)) (.leaf (.ubHLePi 14 3 1 4581))) (.node (.leaf (.ubHLePi 14 4 0 18706)) (.leaf (.ubHLePi 14 0 3 5541))))
            (.node (.node (.leaf (.ubHLePi 14 1 2 28895)) (.leaf (.ubHLePi 14 2 1 13346))) (.node (.leaf (.ubHGe0 14 3 0 24554)) (.leaf (.ubHGe0 14 0 2 10660)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 14 1 1 19980)) (.leaf (.ubHLePi 14 2 0 13948))) (.node (.leaf (.ubHLePi 14 0 1 7803)) (.leaf (.ubHGe0 14 1 0 1395))))
            (.node (.node (.leaf (.ubHGe0 15 0 6 1)) (.leaf (.ubHGe0 15 1 5 60))) (.node (.leaf (.ubHGe0 15 2 4 711)) (.leaf (.ubHGe0 15 3 3 2364))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 15 4 2 1499)) (.leaf (.ubHGe0 15 5 1 220))) (.node (.leaf (.ubHGe0 15 6 0 1549)) (.leaf (.ubHLePi 15 0 5 60))))
            (.node (.node (.leaf (.ubHLePi 15 1 4 1590)) (.leaf (.ubHLePi 15 2 3 9204))) (.node (.leaf (.ubHLePi 15 3 2 12135)) (.leaf (.ubHLePi 15 4 1 3509)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 15 5 0 8369)) (.leaf (.ubHGe0 15 0 4 878))) (.node (.leaf (.ubHGe0 15 1 3 11532)) (.leaf (.ubHGe0 15 2 2 29835))))
            (.node (.node (.leaf (.ubHGe0 15 3 1 17414)) (.leaf (.ubHGe0 15 4 0 20135))) (.node (.leaf (.ubHLePi 15 0 3 4693)) (.leaf (.ubHLePi 15 1 2 29425)))))))))
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 15 2 1 34598)) (.node (.leaf (.ubHLePi 15 3 0 29396)) (.leaf (.ubHGe0 15 0 2 10226))))
            (.node (.node (.leaf (.ubHGe0 15 1 1 29970)) (.leaf (.ubHGe0 15 2 0 28082))) (.node (.leaf (.ubHLePi 15 0 1 9496)) (.leaf (.ubHLePi 15 1 0 15981)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 16 1 5 11)) (.leaf (.ubHGe0 16 2 4 444))) (.node (.leaf (.ubHGe0 16 3 3 4004)) (.leaf (.ubHGe0 16 4 2 12285))))
            (.node (.node (.leaf (.ubHGe0 16 5 1 13163)) (.leaf (.ubHLePi 16 6 0 3045))) (.node (.leaf (.ubHLePi 16 0 5 11)) (.leaf (.ubHLePi 16 1 4 895))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 16 2 3 12924)) (.leaf (.ubHLePi 16 3 2 57078))) (.node (.leaf (.ubHLePi 16 4 1 84322)) (.leaf (.ubHGe0 16 5 0 3403))))
            (.node (.node (.leaf (.ubHGe0 16 0 4 450)) (.leaf (.ubHGe0 16 1 3 13844))) (.node (.leaf (.ubHGe0 16 2 2 98474)) (.leaf (.ubHGe0 16 3 1 211536)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 16 4 0 34173)) (.leaf (.ubHLePi 16 0 3 4923))) (.node (.leaf (.ubHLePi 16 1 2 74854)) (.leaf (.ubHLePi 16 2 1 260806))))
            (.node (.node (.leaf (.ubHLePi 16 3 0 111973)) (.leaf (.ubHGe0 16 0 2 21173))) (.node (.leaf (.ubHGe0 16 1 1 158475)) (.leaf (.ubHGe0 16 2 0 142506)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 16 0 1 38046)) (.node (.leaf (.ubHLePi 16 1 0 84544)) (.leaf (.ubHGe0 16 0 0 19479))))
            (.node (.node (.leaf (.ubHLePi 17 2 4 6)) (.leaf (.ubHLePi 17 3 3 32))) (.node (.leaf (.ubHLePi 17 4 2 131)) (.leaf (.ubHLePi 17 5 1 64)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 17 6 0 4153)) (.leaf (.ubHGe0 17 1 4 10))) (.node (.leaf (.ubHGe0 17 2 3 92)) (.leaf (.ubHGe0 17 3 2 558))))
            (.node (.node (.leaf (.ubHGe0 17 4 1 752)) (.leaf (.ubHLePi 17 5 0 22597))) (.node (.leaf (.ubHLePi 17 0 4 4)) (.leaf (.ubHLePi 17 1 3 89))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 17 2 2 883)) (.leaf (.ubHLePi 17 3 1 2269))) (.node (.leaf (.ubHGe0 17 4 0 51282)) (.leaf (.ubHGe0 17 0 3 29))))
            (.node (.node (.leaf (.ubHGe0 17 1 2 617)) (.leaf (.ubHGe0 17 2 1 2962))) (.node (.leaf (.ubHLePi 17 3 0 62082)) (.leaf (.ubHLePi 17 0 2 161)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 17 1 1 1801)) (.leaf (.ubHGe0 17 2 0 42242))) (.node (.leaf (.ubHGe0 17 0 1 420)) (.leaf (.ubHLePi 17 1 0 15299))))
            (.node (.node (.leaf (.ubHGe0 17 0 0 2301)) (.leaf (.ubHLePi 18 3 3 239))) (.node (.leaf (.ubHLePi 18 4 2 3737)) (.leaf (.ubHLePi 18 5 1 15253))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 18 6 0 4640)) (.node (.leaf (.ubHGe0 18 2 3 670)) (.leaf (.ubHGe0 18 3 2 14679))))
            (.node (.node (.leaf (.ubHGe0 18 4 1 78137)) (.leaf (.ubHGe0 18 5 0 40855))) (.node (.leaf (.ubHLePi 18 1 3 630)) (.leaf (.ubHLePi 18 2 2 21665)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 18 3 1 160330)) (.leaf (.ubHLePi 18 4 0 133666))) (.node (.leaf (.ubHGe0 18 0 3 198)) (.leaf (.ubHGe0 18 1 2 14236))))
            (.node (.node (.leaf (.ubHGe0 18 2 1 164623)) (.leaf (.ubHGe0 18 3 0 219489))) (.node (.leaf (.ubHLePi 18 0 2 3513)) (.leaf (.ubHLePi 18 1 1 84549))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 18 2 0 195295)) (.leaf (.ubHGe0 18 0 1 17372))) (.node (.leaf (.ubHGe0 18 1 0 90371)) (.leaf (.ubHLePi 18 0 0 17112))))
            (.node (.node (.leaf (.ubHLePi 19 4 2 1110)) (.leaf (.ubHGe0 19 5 1 3425))) (.node (.leaf (.ubHGe0 19 6 0 25607)) (.leaf (.ubHGe0 19 3 2 4138)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 19 4 1 13692)) (.leaf (.ubHLePi 19 5 0 145587))) (.node (.leaf (.ubHLePi 19 2 2 5807)) (.leaf (.ubHGe0 19 3 1 21478))))
            (.node (.node (.leaf (.ubHGe0 19 4 0 345572)) (.leaf (.ubHGe0 19 1 2 3637))) (.node (.leaf (.ubHLePi 19 2 1 16333)) (.leaf (.ubHLePi 19 3 0 438097)))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 19 0 2 857)) (.leaf (.ubHGe0 19 1 1 5904))) (.node (.leaf (.ubHGe0 19 2 0 312714)) (.leaf (.ubHLePi 19 0 1 779))))
            (.node (.node (.leaf (.ubHLePi 19 1 0 119120)) (.leaf (.ubHGe0 19 0 0 18912))) (.node (.leaf (.ubHGe0 20 5 1 518)) (.leaf (.ubHGe0 20 6 0 13467)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 20 4 1 2799)) (.leaf (.ubHLePi 20 5 0 75936))) (.node (.leaf (.ubHGe0 20 3 1 5831)) (.leaf (.ubHGe0 20 4 0 179536))))
            (.node (.node (.leaf (.ubHLePi 20 2 1 5947)) (.leaf (.ubHLePi 20 3 0 227579))) (.node (.leaf (.ubHGe0 20 1 1 2993)) (.leaf (.ubHGe0 20 2 0 162990))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 20 0 1 597)) (.leaf (.ubHLePi 20 1 0 62493))) (.node (.leaf (.ubHGe0 20 0 0 10017)) (.leaf (.ubHLePi 21 6 0 15103))))
            (.node (.node (.leaf (.ubHGe0 21 5 0 85317)) (.leaf (.ubHLePi 21 4 0 201498))) (.node (.leaf (.ubHGe0 21 3 0 254572)) (.leaf (.ubHLePi 21 2 0 181403)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 21 1 0 69109)) (.leaf (.ubHLePi 21 0 0 10994))) (.node (.leaf (.ubPHi 6 315414)) (.leaf (.ubPHi 5 352382))))
            (.node (.node (.leaf (.ubPHi 4 4031863)) (.leaf (.ubPHi 3 994375))) (.node (.leaf (.ubPHi 2 3547895)) (.leaf (.eqP0 (-210749)))))))))))))

lemma step2bScale_pos : 0 < step2bScale := by decide
lemma step2bLb_strict : 838 * (step2bScale : ℤ) < 1330 * step2bLb := by decide
lemma step2bCert_u_ok :
    checkBinoBoundU 21 6 [(2, 1), (20, 1), (21, 0)] step2bCert 3 1 step2bScale step2bLb = true := by
  decide
private lemma step2bCert_c_0 : checkBinoCForJ 21 6 0 step2bCert = true := by decide
private lemma step2bCert_c_1 : checkBinoCForJ 21 6 1 step2bCert = true := by decide
private lemma step2bCert_c_2 : checkBinoCForJ 21 6 2 step2bCert = true := by decide
private lemma step2bCert_c_3 : checkBinoCForJ 21 6 3 step2bCert = true := by decide
private lemma step2bCert_c_4 : checkBinoCForJ 21 6 4 step2bCert = true := by decide
private lemma step2bCert_c_5 : checkBinoCForJ 21 6 5 step2bCert = true := by decide
private lemma step2bCert_c_6 : checkBinoCForJ 21 6 6 step2bCert = true := by decide
private lemma step2bCert_c_7 : checkBinoCForJ 21 6 7 step2bCert = true := by decide
private lemma step2bCert_c_8 : checkBinoCForJ 21 6 8 step2bCert = true := by decide
private lemma step2bCert_c_9 : checkBinoCForJ 21 6 9 step2bCert = true := by decide
private lemma step2bCert_c_10 : checkBinoCForJ 21 6 10 step2bCert = true := by decide
private lemma step2bCert_c_11 : checkBinoCForJ 21 6 11 step2bCert = true := by decide
private lemma step2bCert_c_12 : checkBinoCForJ 21 6 12 step2bCert = true := by decide
private lemma step2bCert_c_13 : checkBinoCForJ 21 6 13 step2bCert = true := by decide
private lemma step2bCert_c_14 : checkBinoCForJ 21 6 14 step2bCert = true := by decide
private lemma step2bCert_c_15 : checkBinoCForJ 21 6 15 step2bCert = true := by decide
private lemma step2bCert_c_16 : checkBinoCForJ 21 6 16 step2bCert = true := by decide
private lemma step2bCert_c_17 : checkBinoCForJ 21 6 17 step2bCert = true := by decide
private lemma step2bCert_c_18 : checkBinoCForJ 21 6 18 step2bCert = true := by decide
private lemma step2bCert_c_19 : checkBinoCForJ 21 6 19 step2bCert = true := by decide
private lemma step2bCert_c_20 : checkBinoCForJ 21 6 20 step2bCert = true := by decide
private lemma step2bCert_c_21 : checkBinoCForJ 21 6 21 step2bCert = true := by decide
lemma step2bCert_c_ok : ∀ j ≤ 21, checkBinoCForJ 21 6 j step2bCert = true := by
  intro j hj
  match j with
  | 0 => exact step2bCert_c_0
  | 1 => exact step2bCert_c_1
  | 2 => exact step2bCert_c_2
  | 3 => exact step2bCert_c_3
  | 4 => exact step2bCert_c_4
  | 5 => exact step2bCert_c_5
  | 6 => exact step2bCert_c_6
  | 7 => exact step2bCert_c_7
  | 8 => exact step2bCert_c_8
  | 9 => exact step2bCert_c_9
  | 10 => exact step2bCert_c_10
  | 11 => exact step2bCert_c_11
  | 12 => exact step2bCert_c_12
  | 13 => exact step2bCert_c_13
  | 14 => exact step2bCert_c_14
  | 15 => exact step2bCert_c_15
  | 16 => exact step2bCert_c_16
  | 17 => exact step2bCert_c_17
  | 18 => exact step2bCert_c_18
  | 19 => exact step2bCert_c_19
  | 20 => exact step2bCert_c_20
  | 21 => exact step2bCert_c_21
  | _ + 22 => omega

def step2cScale : ℕ := 50000000000
def step2cLb : ℤ := (-31679263504)
def step2cCert : BinTree BinoStep :=
  (.node
    (.node
      (.node
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.eqP1 (-1741802096175))) (.node (.leaf (.eqB00 0 494817007555)) (.leaf (.eqB00 2 (-340873175590)))))
            (.node (.node (.leaf (.eqB10 2 379955852111)) (.leaf (.eqB01 2 1343542778869))) (.node (.leaf (.eqDiag 3 15489447683)) (.leaf (.eqB00 3 (-317432230391))))))
            (.node
            (.node (.node (.leaf (.eqB01 3 510335278444)) (.leaf (.eqDiag 4 1299524077))) (.node (.leaf (.eqB00 6 (-191662394979))) (.leaf (.eqB10 6 330977895704))))
            (.node (.node (.leaf (.eqB01 6 413277078707)) (.leaf (.eqDiag 7 15279589024))) (.node (.leaf (.eqDiag 8 69111281192)) (.leaf (.eqB00 8 (-383805075278)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqB10 8 215660986659)) (.leaf (.eqB01 8 633105653013))) (.node (.leaf (.eqB00 9 (-265633116455))) (.leaf (.eqB10 9 200075633955))))
            (.node (.node (.leaf (.eqB01 9 196227606492)) (.leaf (.eqDiag 10 177896892144))) (.node (.leaf (.eqDiag 12 50997886763)) (.leaf (.eqB00 12 (-535617972651))))))
            (.node
            (.node (.node (.leaf (.eqB10 12 839295134488)) (.leaf (.eqB01 12 658465417998))) (.node (.leaf (.eqB00 13 (-279853284462))) (.leaf (.eqB10 13 353993449798))))
            (.node (.node (.leaf (.eqB01 13 323992925769)) (.leaf (.eqDiag 15 47890281228))) (.node (.leaf (.eqDiag 17 3686378645)) (.leaf (.eqB01 17 115464164197)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.eqDiag 18 5149098140)) (.node (.leaf (.eqB01 18 7482180142)) (.leaf (.eqB00 19 (-176788854263)))))
            (.node (.node (.leaf (.eqB10 19 435726057321)) (.leaf (.eqB10 20 173561356001))) (.node (.leaf (.eqB01 20 141126263820)) (.leaf (.eqDiag 21 3296650992)))))
            (.node
            (.node (.node (.leaf (.eqB00 21 2577751959)) (.leaf (.eqSym 0 5 0 (-12002701465)))) (.node (.leaf (.eqSym 0 9 0 14144597686)) (.leaf (.eqSym 0 15 0 (-21338135937)))))
            (.node (.node (.leaf (.eqSym 0 19 0 84229483962)) (.leaf (.eqSym 0 20 0 (-102913114950)))) (.node (.leaf (.eqSym 0 21 0 33340837402)) (.leaf (.eqSym 1 2 1 (-475098787829)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 1 3 1 522696000948)) (.leaf (.eqSym 1 5 1 (-222145800403)))) (.node (.leaf (.eqSym 1 9 1 86550311845)) (.leaf (.eqSym 1 11 1 (-39492586738)))))
            (.node (.node (.leaf (.eqSym 1 20 1 3556889321)) (.leaf (.eqSym 1 21 1 (-2338376846)))) (.node (.leaf (.eqSym 2 3 1 (-819525271769))) (.leaf (.eqSym 2 3 2 (-109850746026))))))
            (.node
            (.node (.node (.leaf (.eqSym 2 4 1 795595118727)) (.leaf (.eqSym 2 4 2 24199958217))) (.node (.leaf (.eqSym 2 5 2 202468908784)) (.leaf (.eqSym 2 6 0 (-243336727980)))))
            (.node (.node (.leaf (.eqSym 2 6 1 (-471668428804))) (.leaf (.eqSym 2 6 2 (-79453057658)))) (.node (.leaf (.eqSym 2 7 1 288124525632)) (.leaf (.eqSym 2 9 0 150636363621))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 2 11 1 1055675587848)) (.node (.leaf (.eqSym 2 11 2 (-157262228371))) (.leaf (.eqSym 2 12 1 (-884376534434)))))
            (.node (.node (.leaf (.eqSym 2 13 1 (-225029376849))) (.leaf (.eqSym 2 14 0 61568146169))) (.node (.leaf (.eqSym 2 15 1 119908914634)) (.leaf (.eqSym 2 16 1 (-313863572073))))))
            (.node
            (.node (.node (.leaf (.eqSym 2 17 0 (-128944889681))) (.leaf (.eqSym 2 17 1 150058646919))) (.node (.leaf (.eqSym 2 17 2 480033512424)) (.leaf (.eqSym 2 19 0 59024161815))))
            (.node (.node (.leaf (.eqSym 2 19 1 565124711774)) (.leaf (.eqSym 2 19 2 (-544141941074)))) (.node (.leaf (.eqSym 2 20 1 (-390681294116))) (.leaf (.eqSym 2 21 2 170202933212))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 3 4 0 314215011709)) (.leaf (.eqSym 3 4 1 (-505048255189)))) (.node (.leaf (.eqSym 3 5 0 (-70778807060))) (.leaf (.eqSym 3 5 1 489836072514))))
            (.node (.node (.leaf (.eqSym 3 5 2 (-311433099410))) (.leaf (.eqSym 3 5 3 19712180605))) (.node (.leaf (.eqSym 3 8 1 (-847886480261))) (.leaf (.eqSym 3 8 2 347297478047)))))
            (.node
            (.node (.node (.leaf (.eqSym 3 8 3 (-91881257890))) (.leaf (.eqSym 3 9 0 (-143895736232)))) (.node (.leaf (.eqSym 3 9 1 (-65651131604))) (.leaf (.eqSym 3 9 2 (-211177986616)))))
            (.node (.node (.leaf (.eqSym 3 10 0 69110756366)) (.leaf (.eqSym 3 10 1 1192553604218))) (.node (.leaf (.eqSym 3 10 3 311926288906)) (.leaf (.eqSym 3 11 0 67378166673)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 3 11 1 (-487053616260))) (.node (.leaf (.eqSym 3 11 2 124871519300)) (.leaf (.eqSym 3 12 3 (-280824163594)))))
            (.node (.node (.leaf (.eqSym 3 13 1 (-243339927961))) (.leaf (.eqSym 3 14 0 (-67358111726)))) (.node (.leaf (.eqSym 3 15 1 121520259442)) (.leaf (.eqSym 3 17 0 22347005869)))))
            (.node
            (.node (.node (.leaf (.eqSym 3 17 1 186641583291)) (.leaf (.eqSym 3 17 2 13566474210))) (.node (.leaf (.eqSym 3 18 0 1236998610)) (.leaf (.eqSym 3 18 1 (-57998335924)))))
            (.node (.node (.leaf (.eqSym 3 18 2 50392891389)) (.leaf (.eqSym 3 19 1 (-79476956485)))) (.node (.leaf (.eqSym 3 19 2 (-415757700215))) (.leaf (.eqSym 3 19 3 124885937988))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 3 20 2 292389677269)) (.leaf (.eqSym 3 20 3 (-21682055392)))) (.node (.leaf (.eqSym 3 21 3 (-72657477936))) (.leaf (.eqSym 4 5 2 84043982990))))
            (.node (.node (.leaf (.eqSym 4 7 0 162920141945)) (.leaf (.eqSym 4 7 4 75724534237))) (.node (.leaf (.eqSym 4 8 4 (-147781817159))) (.leaf (.eqSym 4 9 1 (-39610612746))))))
            (.node
            (.node (.node (.leaf (.eqSym 4 9 2 (-184384275994))) (.leaf (.eqSym 4 10 0 (-83643393849)))) (.node (.leaf (.eqSym 4 10 4 116613406817)) (.leaf (.eqSym 4 11 2 142679908902))))
            (.node (.node (.leaf (.eqSym 4 13 1 6826142737)) (.leaf (.eqSym 4 13 4 (-107380020637)))) (.node (.leaf (.eqSym 4 14 0 11688663850)) (.leaf (.eqSym 4 14 4 67360418523)))))))))
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 4 15 0 10192688165)) (.node (.leaf (.eqSym 4 17 0 (-6239896252))) (.leaf (.eqSym 4 17 1 1279362342))))
            (.node (.node (.leaf (.eqSym 4 17 2 (-54553164090))) (.leaf (.eqSym 4 18 2 46293344737))) (.node (.leaf (.eqSym 4 19 2 (-9879838328))) (.leaf (.eqSym 4 19 4 (-8881188790))))))
            (.node
            (.node (.node (.leaf (.eqSym 4 20 4 5644191086)) (.leaf (.eqSym 5 6 1 389122638966))) (.node (.leaf (.eqSym 5 6 3 73115003044)) (.leaf (.eqSym 5 6 5 (-35732006146)))))
            (.node (.node (.leaf (.eqSym 5 8 0 (-269852287643))) (.leaf (.eqSym 5 8 1 (-189947610957)))) (.node (.leaf (.eqSym 5 8 3 (-71417941095))) (.leaf (.eqSym 5 8 4 62293321307))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 5 8 5 182083152010)) (.leaf (.eqSym 5 9 0 87436541150))) (.node (.leaf (.eqSym 5 9 2 26295636446)) (.leaf (.eqSym 5 9 5 (-152474654820)))))
            (.node (.node (.leaf (.eqSym 5 10 4 (-79274824063))) (.leaf (.eqSym 5 10 5 (-381044468326)))) (.node (.leaf (.eqSym 5 11 0 277158906798)) (.leaf (.eqSym 5 11 1 413840548305)))))
            (.node
            (.node (.node (.leaf (.eqSym 5 11 2 (-76558667022))) (.leaf (.eqSym 5 11 4 (-8438607024)))) (.node (.leaf (.eqSym 5 11 5 438272820460)) (.leaf (.eqSym 5 12 0 (-166623329823)))))
            (.node (.node (.leaf (.eqSym 5 12 1 (-447902723663))) (.leaf (.eqSym 5 12 3 21499600307))) (.node (.leaf (.eqSym 5 13 1 89782981054)) (.leaf (.eqSym 5 13 4 (-40246716989))))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 5 15 1 (-11488296601))) (.node (.leaf (.eqSym 5 15 2 14623917461)) (.leaf (.eqSym 5 16 1 15710472261))))
            (.node (.node (.leaf (.eqSym 5 16 4 112412013435)) (.leaf (.eqSym 5 16 5 (-46592545760)))) (.node (.leaf (.eqSym 5 17 5 (-73749363466))) (.leaf (.eqSym 5 18 2 10718905478)))))
            (.node
            (.node (.node (.leaf (.eqSym 5 19 3 (-3484481651))) (.leaf (.eqSym 5 19 4 (-49645983903)))) (.node (.leaf (.eqSym 5 19 5 47774574949)) (.leaf (.eqSym 6 7 3 55176220706))))
            (.node (.node (.leaf (.eqSym 6 7 5 (-226946954990))) (.leaf (.eqSym 6 8 1 446654046753))) (.node (.leaf (.eqSym 6 8 3 (-113765870782))) (.leaf (.eqSym 6 8 5 (-73450334993)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 6 9 0 (-65387782246))) (.leaf (.eqSym 6 9 5 629321051231))) (.node (.leaf (.eqSym 6 9 6 (-25269529462))) (.leaf (.eqSym 6 11 1 (-452351353419)))))
            (.node (.node (.leaf (.eqSym 6 11 2 (-233810927433))) (.leaf (.eqSym 6 11 5 (-420367877172)))) (.node (.leaf (.eqSym 6 12 0 35651159828)) (.leaf (.eqSym 6 12 1 489668780815)))))
            (.node
            (.node (.node (.leaf (.eqSym 6 12 3 346686252467)) (.leaf (.eqSym 6 13 0 41724609933))) (.node (.leaf (.eqSym 6 13 1 (-247100595099))) (.leaf (.eqSym 6 13 4 42000651600))))
            (.node (.node (.leaf (.eqSym 6 13 6 9089827851)) (.leaf (.eqSym 6 14 0 (-33710031768)))) (.node (.leaf (.eqSym 6 14 2 154357869775)) (.leaf (.eqSym 6 14 3 (-140008502595)))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 6 15 1 12008952195)) (.node (.leaf (.eqSym 6 15 3 (-224927204091))) (.leaf (.eqSym 6 16 1 (-447725379)))))
            (.node (.node (.leaf (.eqSym 6 16 3 149954107339)) (.leaf (.eqSym 6 19 4 (-42000651600)))) (.node (.leaf (.eqSym 6 19 5 55712109779)) (.leaf (.eqSym 6 19 6 223701771430)))))
            (.node
            (.node (.node (.leaf (.eqSym 6 20 6 (-331564872384))) (.leaf (.eqSym 7 8 1 105382442453))) (.node (.leaf (.eqSym 7 8 2 578819859875)) (.leaf (.eqSym 7 8 7 (-98826394736)))))
            (.node (.node (.leaf (.eqSym 7 9 0 (-39046656880))) (.leaf (.eqSym 7 9 4 154909099724))) (.node (.leaf (.eqSym 7 9 6 (-825975753936))) (.leaf (.eqSym 7 9 7 321970176378))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 7 10 0 369045762200)) (.leaf (.eqSym 7 10 2 (-875632117797)))) (.node (.leaf (.eqSym 7 10 3 213644532328)) (.leaf (.eqSym 7 10 4 (-503938622943)))))
            (.node (.node (.leaf (.eqSym 7 10 6 767322018172)) (.leaf (.eqSym 7 10 7 (-22529075013)))) (.node (.leaf (.eqSym 7 11 0 (-321502380972))) (.leaf (.eqSym 7 11 7 (-186468746294))))))
            (.node
            (.node (.node (.leaf (.eqSym 7 12 6 73655849003)) (.leaf (.eqSym 7 13 1 97401832175))) (.node (.leaf (.eqSym 7 13 3 410858954107)) (.leaf (.eqSym 7 14 0 21594581305))))
            (.node (.node (.leaf (.eqSym 7 14 3 (-20327923673))) (.leaf (.eqSym 7 14 7 (-60742490209)))) (.node (.leaf (.eqSym 7 15 1 (-12009088627))) (.leaf (.eqSym 7 15 7 29825407285)))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 7 16 3 (-67962018569))) (.leaf (.eqSym 7 17 3 13649773050))) (.node (.leaf (.eqSym 7 17 4 (-69933039081))) (.leaf (.eqSym 7 17 5 60529805192))))
            (.node (.node (.leaf (.eqSym 7 17 6 (-35913214078))) (.leaf (.eqSym 7 17 7 (-114305321965)))) (.node (.leaf (.eqSym 7 18 5 9463127963)) (.leaf (.eqSym 7 18 6 (-322737143201))))))
            (.node
            (.node (.node (.leaf (.eqSym 7 18 7 354592479303)) (.leaf (.eqSym 7 19 6 277263415676))) (.node (.leaf (.eqSym 7 19 7 (-194102528680))) (.leaf (.eqSym 8 9 2 23484260120))))
            (.node (.node (.leaf (.eqSym 8 9 4 77073017094)) (.leaf (.eqSym 8 9 6 (-145629019079)))) (.node (.leaf (.eqSym 8 10 0 (-230879992673))) (.leaf (.eqSym 8 10 2 266600483483))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 8 10 8 151929222763)) (.leaf (.eqSym 8 11 0 168162218089))) (.node (.leaf (.eqSym 8 11 3 345596993747)) (.leaf (.eqSym 8 11 4 (-92181785334)))))
            (.node (.node (.leaf (.eqSym 8 11 7 (-65765337402))) (.leaf (.eqSym 8 11 8 (-112340717475)))) (.node (.leaf (.eqSym 8 12 1 80303929272)) (.leaf (.eqSym 8 12 3 118185246950)))))
            (.node
            (.node (.node (.leaf (.eqSym 8 12 6 203044640405)) (.leaf (.eqSym 8 13 1 (-92272938961)))) (.node (.leaf (.eqSym 8 13 3 (-41926835269))) (.leaf (.eqSym 8 13 4 (-170459775148)))))
            (.node (.node (.leaf (.eqSym 8 14 2 9509165607)) (.leaf (.eqSym 8 14 7 (-41240866029)))) (.node (.leaf (.eqSym 8 16 4 (-80912568670))) (.leaf (.eqSym 8 16 5 (-300699472247)))))))))))
      (.node
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 8 16 8 127911153428)) (.node (.leaf (.eqSym 8 19 6 424313714421)) (.leaf (.eqSym 8 19 7 424816605731))))
            (.node (.node (.leaf (.eqSym 8 19 8 (-521123920795))) (.leaf (.eqSym 8 20 7 (-633434661854)))) (.node (.leaf (.eqSym 8 20 8 458959251897)) (.leaf (.eqSym 9 10 0 33003955372)))))
            (.node
            (.node (.node (.leaf (.eqSym 9 10 1 (-317738901206))) (.leaf (.eqSym 9 10 7 (-869873545098)))) (.node (.leaf (.eqSym 9 10 9 (-258430618764))) (.leaf (.eqSym 9 11 0 (-47411768677)))))
            (.node (.node (.leaf (.eqSym 9 11 1 298740854069)) (.leaf (.eqSym 9 11 8 646780139674))) (.node (.leaf (.eqSym 9 11 9 (-37541024148))) (.leaf (.eqSym 9 12 1 (-45427348544)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 9 12 6 328238096465)) (.leaf (.eqSym 9 12 9 33905515812))) (.node (.leaf (.eqSym 9 13 1 6012896944)) (.leaf (.eqSym 9 13 4 (-41858924025)))))
            (.node (.node (.leaf (.eqSym 9 14 7 78530058094)) (.leaf (.eqSym 9 15 5 88131237783))) (.node (.leaf (.eqSym 9 16 8 (-199401007565))) (.leaf (.eqSym 9 18 7 201765762706)))))
            (.node
            (.node (.node (.leaf (.eqSym 9 18 8 159954876850)) (.leaf (.eqSym 9 18 9 (-604415025955)))) (.node (.leaf (.eqSym 9 19 7 (-380743321756))) (.leaf (.eqSym 9 19 8 (-925920584187)))))
            (.node (.node (.leaf (.eqSym 9 19 9 1015647398787)) (.leaf (.eqSym 9 20 8 889641375151))) (.node (.leaf (.eqSym 9 20 9 (-92350192972))) (.leaf (.eqSym 10 11 0 (-5924839983))))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 10 11 2 (-217473892845))) (.node (.leaf (.eqSym 10 11 7 29969004967)) (.leaf (.eqSym 10 11 9 (-550587659411)))))
            (.node (.node (.leaf (.eqSym 10 11 10 253226917700)) (.leaf (.eqSym 10 12 1 (-12070492319)))) (.node (.leaf (.eqSym 10 12 3 (-428868853167))) (.leaf (.eqSym 10 12 6 (-571989814485))))))
            (.node
            (.node (.node (.leaf (.eqSym 10 12 7 (-477702165272))) (.leaf (.eqSym 10 13 3 262224259332))) (.node (.leaf (.eqSym 10 13 8 207382248357)) (.leaf (.eqSym 10 13 9 98978081653))))
            (.node (.node (.leaf (.eqSym 10 14 7 189405094567)) (.leaf (.eqSym 10 15 7 405082040269))) (.node (.leaf (.eqSym 10 15 8 (-128537375552))) (.leaf (.eqSym 10 16 6 287165218770))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 10 16 10 (-72491706632))) (.leaf (.eqSym 10 17 8 (-86871386429)))) (.node (.leaf (.eqSym 10 17 9 227813644201)) (.leaf (.eqSym 10 17 10 151735859186))))
            (.node (.node (.leaf (.eqSym 10 18 7 (-97338433522))) (.leaf (.eqSym 10 18 10 (-130566841997)))) (.node (.leaf (.eqSym 10 19 8 (-272171916281))) (.leaf (.eqSym 10 19 9 (-307216573560))))))
            (.node
            (.node (.node (.leaf (.eqSym 10 20 9 371074343432)) (.leaf (.eqSym 10 20 10 (-3993491437)))) (.node (.leaf (.eqSym 11 12 3 232828623783)) (.leaf (.eqSym 11 12 4 (-95610559669)))))
            (.node (.node (.leaf (.eqSym 11 12 6 323467125772)) (.leaf (.eqSym 11 12 9 (-4714735642)))) (.node (.leaf (.eqSym 11 12 11 (-67790319731))) (.leaf (.eqSym 11 13 4 (-212718799213)))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 11 13 10 (-114317702470))) (.node (.leaf (.eqSym 11 14 4 (-95928819576))) (.leaf (.eqSym 11 14 7 (-198515203860)))))
            (.node (.node (.leaf (.eqSym 11 14 9 (-56986798563))) (.leaf (.eqSym 11 14 11 48449624492))) (.node (.leaf (.eqSym 11 15 5 69886697938)) (.leaf (.eqSym 11 15 8 (-340673170862))))))
            (.node
            (.node (.node (.leaf (.eqSym 11 15 11 (-12323472557))) (.leaf (.eqSym 11 16 6 36144904629))) (.node (.leaf (.eqSym 11 16 8 175288400137)) (.leaf (.eqSym 11 16 10 123273637716))))
            (.node (.node (.leaf (.eqSym 11 17 7 (-8774854104))) (.leaf (.eqSym 11 17 8 64271672468))) (.node (.leaf (.eqSym 11 17 10 (-156782723918))) (.leaf (.eqSym 11 17 11 (-55219835964)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 11 18 9 (-268272970341))) (.leaf (.eqSym 11 18 10 467650747033))) (.node (.leaf (.eqSym 11 18 11 449587607752)) (.leaf (.eqSym 11 19 9 367696870860))))
            (.node (.node (.leaf (.eqSym 11 19 10 501044106679)) (.leaf (.eqSym 11 19 11 (-730074122904)))) (.node (.leaf (.eqSym 11 20 10 (-818830807323))) (.leaf (.eqSym 11 20 11 (-83520493794))))))
            (.node
            (.node (.node (.leaf (.eqSym 11 21 11 (-2083597943))) (.leaf (.eqSym 12 13 4 7566896903))) (.node (.leaf (.eqSym 12 13 9 (-117843967285))) (.leaf (.eqSym 12 13 10 (-63232176592)))))
            (.node (.node (.leaf (.eqSym 12 13 12 31902293532)) (.leaf (.eqSym 12 15 7 (-65544002362)))) (.node (.leaf (.eqSym 12 16 8 (-92411294070))) (.leaf (.eqSym 12 17 11 21404025780)))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 12 18 9 107724566640)) (.leaf (.eqSym 12 18 11 (-25209851607)))) (.node (.leaf (.eqSym 12 19 11 92523637132)) (.leaf (.eqSym 12 20 11 (-76458866070)))))
            (.node (.node (.leaf (.eqSym 13 14 6 153708745654)) (.leaf (.eqSym 13 14 7 34586187771))) (.node (.leaf (.eqSym 13 15 7 (-147976874481))) (.leaf (.eqSym 13 15 10 161301385118)))))
            (.node
            (.node (.node (.leaf (.eqSym 13 16 8 (-55815168038))) (.leaf (.eqSym 13 16 9 (-63964343691)))) (.node (.leaf (.eqSym 13 16 13 (-36134165140))) (.leaf (.eqSym 13 17 12 (-38779942899)))))
            (.node (.node (.leaf (.eqSym 13 18 12 (-410767391895))) (.leaf (.eqSym 13 19 12 82344616003))) (.node (.leaf (.eqSym 13 19 13 228558901396)) (.leaf (.eqSym 13 20 12 206521644004))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 14 15 8 92876756961)) (.leaf (.eqSym 14 15 11 (-58637857195)))) (.node (.leaf (.eqSym 14 15 13 85186172545)) (.leaf (.eqSym 14 15 14 (-53685331036)))))
            (.node (.node (.leaf (.eqSym 14 17 14 (-17961519753))) (.leaf (.eqSym 14 18 14 5841263288))) (.node (.leaf (.eqSym 14 20 13 (-651274416549))) (.leaf (.eqSym 14 20 14 10385321610)))))
            (.node
            (.node (.node (.leaf (.eqSym 14 21 14 4117282467)) (.leaf (.eqSym 15 16 10 (-12009103473)))) (.node (.leaf (.eqSym 15 16 12 (-11004100446))) (.leaf (.eqSym 15 16 14 (-7017116110)))))
            (.node (.node (.leaf (.eqSym 15 16 15 60260900663)) (.leaf (.eqSym 15 17 14 (-3063739921)))) (.node (.leaf (.eqSym 15 18 14 97839729793)) (.leaf (.eqSym 15 18 15 (-40167149380))))))))))
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.eqSym 15 19 14 (-32811040392))) (.node (.leaf (.eqSym 15 20 14 3204950880)) (.leaf (.eqSym 15 20 15 (-20724009775)))))
            (.node (.node (.leaf (.eqSym 15 21 15 11581644383)) (.leaf (.eqSym 16 19 14 (-125948930160)))) (.node (.leaf (.eqSym 16 19 15 52572333922)) (.leaf (.eqSym 16 19 16 13538934783)))))
            (.node
            (.node (.node (.leaf (.eqSym 16 20 15 (-587891868961))) (.leaf (.eqSym 16 20 16 (-68185981753)))) (.node (.leaf (.eqSym 17 18 15 51719439816)) (.leaf (.eqSym 17 18 16 (-79580068840)))))
            (.node (.node (.leaf (.eqSym 17 18 17 (-7647928443))) (.leaf (.eqSym 17 19 15 (-1364977305)))) (.node (.leaf (.eqSym 17 19 16 (-33754438217))) (.leaf (.eqSym 17 19 17 56382017122))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 18 19 17 (-162132555239))) (.leaf (.eqSym 18 19 18 (-54974030336)))) (.node (.leaf (.eqSym 18 20 17 92566793643)) (.leaf (.eqSym 18 20 18 145102924196))))
            (.node (.node (.leaf (.eqSym 18 21 18 (-70224756437))) (.leaf (.eqSym 19 20 18 (-121484987818)))) (.node (.leaf (.eqSym 19 20 19 (-62981608152))) (.leaf (.eqSym 19 21 19 90794925196)))))
            (.node
            (.node (.node (.leaf (.eqSym 20 21 20 (-36327469259))) (.leaf (.eqPFix 2 1 3112780985022))) (.node (.leaf (.eqPFix 20 1 1422389725048)) (.leaf (.eqPFix 21 0 (-476596385281)))))
            (.node (.node (.leaf (.ubHLePi 0 0 0 488827355362)) (.leaf (.ubHLePj 0 0 1 10528685495))) (.node (.leaf (.ubHLePi 1 1 0 126272356797)) (.leaf (.ubHLePi 2 0 2 1321449444261)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHMcc 2 0 7 905918854372)) (.node (.leaf (.ubHLePi 2 0 8 713457314358)) (.leaf (.ubHMcc 2 0 16 76871488611))))
            (.node (.node (.leaf (.ubHLePi 2 0 17 51606133700)) (.leaf (.ubHLePi 2 1 1 169822415101))) (.node (.leaf (.ubHMcc 2 1 4 134308378307)) (.leaf (.ubHLePi 2 2 0 12167175506)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 2 2 2 1635485387)) (.leaf (.ubHLePi 3 0 17 647763844))) (.node (.leaf (.ubHMcc 3 1 18 926086603)) (.leaf (.ubHLePj 3 3 17 26009994997))))
            (.node (.node (.leaf (.ubHGe0 4 0 0 208887792051)) (.leaf (.ubHLePj 4 0 1 428184599900))) (.node (.leaf (.ubHLePj 4 1 0 322051971205)) (.leaf (.ubHGe0 5 0 0 127725027011))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePj 5 0 1 117668242244)) (.leaf (.ubHGe0 5 0 5 493414521))) (.node (.leaf (.ubHGe0 5 0 14 351155495)) (.leaf (.ubHLePj 5 1 0 8572262746))))
            (.node (.node (.leaf (.ubHLePj 5 4 15 2900797236)) (.leaf (.ubHLePi 5 5 0 14060140820))) (.node (.leaf (.ubHLePj 5 5 14 7402350281)) (.leaf (.ubHLePi 6 6 0 8765154727)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 6 6 15 115277647839)) (.leaf (.ubHGe0 7 0 0 178916895404))) (.node (.leaf (.ubHLePj 7 0 1 297304439000)) (.leaf (.ubHLePj 7 0 11 307375652))))
            (.node (.node (.leaf (.ubHLePj 7 1 0 196286758939)) (.leaf (.ubHGe0 7 5 0 127630224))) (.node (.leaf (.ubHMcc 7 6 14 32552590944)) (.leaf (.ubHLePj 8 8 1 564564406))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePj 8 8 2 206574040)) (.node (.leaf (.ubHLePi 9 9 0 175207061260)) (.leaf (.ubHGe0 9 9 12 330458926399))))
            (.node (.node (.leaf (.ubHGe0 10 0 0 684759400359)) (.leaf (.ubHLePj 10 0 1 858489242209))) (.node (.leaf (.ubHMcc 10 0 9 132271558)) (.leaf (.ubHLePj 10 1 0 669288796734)))))
            (.node
            (.node (.node (.leaf (.ubHLePj 10 1 1 111610299280)) (.leaf (.ubHLePi 10 3 11 90941471))) (.node (.leaf (.ubHMcc 10 10 2 1913987929)) (.leaf (.ubHMcc 10 10 10 26263535155))))
            (.node (.node (.leaf (.ubHGe0 11 0 0 428620939675)) (.leaf (.ubHLePj 11 0 1 617637497826))) (.node (.leaf (.ubHLePj 11 0 10 32133740)) (.leaf (.ubHLePj 11 1 0 535423845094))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHMcc 11 2 0 1977685409)) (.leaf (.ubHLePi 11 11 0 104103672733))) (.node (.leaf (.ubHLePi 11 11 10 386770015415)) (.leaf (.ubHMcc 12 2 9 1126241053))))
            (.node (.node (.leaf (.ubHMcc 12 12 7 2920773815)) (.leaf (.ubHLePj 13 2 8 1308302251))) (.node (.leaf (.ubHLePj 13 12 0 1253287143)) (.leaf (.ubHLePi 13 13 0 15300810123)))))
            (.node
            (.node (.node (.leaf (.ubHLePj 13 13 7 23113480191)) (.leaf (.ubHGe0 13 13 8 162402462728))) (.node (.leaf (.ubHGe0 14 0 0 18147093241)) (.leaf (.ubHLePj 14 0 1 12444465006))))
            (.node (.node (.leaf (.ubHLePj 14 1 0 43134942273)) (.leaf (.ubHLePj 14 11 0 1466146005))) (.node (.leaf (.ubHLePj 14 13 7 633654884503)) (.leaf (.ubHLePi 14 14 0 28613557769)))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 14 14 2 2074766845)) (.leaf (.ubHGe0 15 0 0 103513095762))) (.node (.leaf (.ubHLePj 15 0 1 144834186516)) (.leaf (.ubHLePj 15 1 0 93881844745))))
            (.node (.node (.leaf (.ubHGe0 16 0 0 46326442789)) (.leaf (.ubHLePj 16 0 1 40330782637))) (.node (.leaf (.ubHLePj 16 1 0 51260164942)) (.leaf (.ubHMcc 16 1 1 324926827234)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 16 2 5 394629756)) (.leaf (.ubHGe0 16 11 5 159147574))) (.node (.leaf (.ubHLePj 16 15 4 13239113862)) (.leaf (.ubHLePj 16 15 5 682267484189))))
            (.node (.node (.leaf (.ubHLePi 16 16 0 28019914405)) (.leaf (.ubHGe0 17 0 0 138110801326))) (.node (.leaf (.ubHLePj 17 1 0 512330510432)) (.leaf (.ubHLePj 17 1 1 301415262934))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 18 0 0 21066290294)) (.leaf (.ubHLePj 18 1 0 49020604029))) (.node (.leaf (.ubHLePi 18 17 0 4419188890)) (.leaf (.ubHLePj 19 0 1 216701371947))))
            (.node (.node (.leaf (.ubHMcc 19 9 1 6276632094)) (.leaf (.ubHLePi 19 13 2 5091034294))) (.node (.leaf (.ubHMcc 19 17 2 38437298141)) (.leaf (.ubHMcc 19 18 1 23280470717)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 19 19 0 358490896)) (.leaf (.ubHMcc 20 14 1 1247204385231))) (.node (.leaf (.ubHLePi 20 20 0 9294113501)) (.leaf (.ubHLePj 21 1 0 132280347190))))
            (.node (.node (.leaf (.ubHGe0 0 0 6 18051)) (.leaf (.ubHLePi 0 0 5 101512))) (.node (.leaf (.ubHGe0 0 0 4 238833)) (.leaf (.ubHLePi 0 0 3 300755)))))))))))
    (.node
      (.node
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHGe0 0 0 2 213705)) (.node (.leaf (.ubHLePi 0 0 1 81214)) (.leaf (.ubHGe0 0 0 0 12892))))
            (.node (.node (.leaf (.ubHGe0 1 0 6 23092)) (.leaf (.ubHGe0 1 1 5 9548))) (.node (.leaf (.ubHLePi 1 0 5 138552)) (.leaf (.ubHLePi 1 1 4 44647)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 1 0 4 346380)) (.leaf (.ubHGe0 1 1 3 83865))) (.node (.leaf (.ubHLePi 1 0 3 461840)) (.leaf (.ubHLePi 1 1 2 79062))))
            (.node (.node (.leaf (.ubHGe0 1 0 2 346380)) (.leaf (.ubHGe0 1 1 1 37391))) (.node (.leaf (.ubHLePi 1 0 1 138552)) (.leaf (.ubHGe0 1 0 0 23092))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 2 0 6 26904)) (.leaf (.ubHGe0 2 1 5 8293))) (.node (.leaf (.ubHLePi 2 2 4 52)) (.leaf (.ubHLePi 2 0 5 156690))))
            (.node (.node (.leaf (.ubHLePi 2 1 4 38314)) (.leaf (.ubHGe0 2 2 3 224))) (.node (.leaf (.ubHGe0 2 0 4 381785)) (.leaf (.ubHGe0 2 1 3 71176)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 2 0 3 497717)) (.leaf (.ubHLePi 2 1 2 66413))) (.node (.leaf (.ubHGe0 2 2 1 229)) (.leaf (.ubHGe0 2 0 2 365918))))
            (.node (.node (.leaf (.ubHGe0 2 1 1 31108)) (.leaf (.ubHLePi 2 0 1 143779))) (.node (.leaf (.ubHLePi 2 1 0 5849)) (.leaf (.ubHGe0 2 0 0 23580)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 3 0 6 24246)) (.node (.leaf (.ubHLePi 3 1 5 17689)) (.leaf (.ubHLePi 3 2 4 3037))))
            (.node (.node (.leaf (.ubHLePi 3 3 3 182)) (.leaf (.ubHGe0 3 0 5 152178))) (.node (.leaf (.ubHGe0 3 1 4 88431)) (.leaf (.ubHGe0 3 2 3 12012)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 3 3 2 525)) (.leaf (.ubHLePi 3 0 4 397943))) (.node (.leaf (.ubHLePi 3 1 3 177514)) (.leaf (.ubHLePi 3 2 2 17828))))
            (.node (.node (.leaf (.ubHLePi 3 3 1 503)) (.leaf (.ubHGe0 3 0 3 554961))) (.node (.leaf (.ubHGe0 3 1 2 178706)) (.leaf (.ubHGe0 3 2 1 11769))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 3 3 0 161)) (.leaf (.ubHLePi 3 0 2 435296))) (.node (.leaf (.ubHLePi 3 1 1 90168)) (.leaf (.ubHLePi 3 2 0 2916))))
            (.node (.node (.leaf (.ubHGe0 3 0 1 182071)) (.leaf (.ubHGe0 3 1 0 18233))) (.node (.leaf (.ubHLePi 3 0 0 31725)) (.leaf (.ubHLePi 4 0 6 17411)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 4 1 5 11240)) (.leaf (.ubHLePi 4 2 4 3284))) (.node (.leaf (.ubHLePi 4 3 3 388)) (.leaf (.ubHLePi 4 4 2 15))))
            (.node (.node (.leaf (.ubHGe0 4 0 5 106980)) (.leaf (.ubHGe0 4 1 4 58563))) (.node (.leaf (.ubHGe0 4 2 3 13416)) (.leaf (.ubHGe0 4 3 2 1164))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHGe0 4 4 1 30)) (.node (.leaf (.ubHLePi 4 0 4 276133)) (.leaf (.ubHLePi 4 1 3 122356))))
            (.node (.node (.leaf (.ubHLePi 4 2 2 20594)) (.leaf (.ubHLePi 4 3 1 1164))) (.node (.leaf (.ubHLePi 4 4 0 15)) (.leaf (.ubHGe0 4 0 3 382650)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 4 1 2 128073)) (.leaf (.ubHGe0 4 2 1 14072))) (.node (.leaf (.ubHGe0 4 3 0 388)) (.leaf (.ubHLePi 4 0 2 299871))))
            (.node (.node (.leaf (.ubHLePi 4 1 1 67131)) (.leaf (.ubHLePi 4 2 0 3610))) (.node (.leaf (.ubHGe0 4 0 1 125879)) (.leaf (.ubHGe0 4 1 0 14091))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 4 0 0 22095)) (.leaf (.ubHGe0 5 0 6 6276))) (.node (.leaf (.ubHGe0 5 1 5 10041)) (.leaf (.ubHGe0 5 2 4 5342))))
            (.node (.node (.leaf (.ubHGe0 5 3 3 1090)) (.leaf (.ubHGe0 5 4 2 84))) (.node (.leaf (.ubHGe0 5 5 1 2)) (.leaf (.ubHLePi 5 0 5 44135)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 5 1 4 56751)) (.leaf (.ubHLePi 5 2 3 23082))) (.node (.leaf (.ubHLePi 5 3 2 3396)) (.leaf (.ubHLePi 5 4 1 172))))
            (.node (.node (.leaf (.ubHGe0 5 0 4 129261)) (.leaf (.ubHGe0 5 1 3 127953))) (.node (.leaf (.ubHGe0 5 2 2 37336)) (.leaf (.ubHGe0 5 3 1 3526)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHGe0 5 4 0 87)) (.node (.leaf (.ubHLePi 5 0 3 201489)) (.leaf (.ubHLePi 5 1 2 143796))))
            (.node (.node (.leaf (.ubHLePi 5 2 1 26799)) (.leaf (.ubHLePi 5 3 0 1220))) (.node (.leaf (.ubHGe0 5 0 2 176128)) (.leaf (.ubHGe0 5 1 1 80541)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 5 2 0 7202)) (.leaf (.ubHLePi 5 0 1 81817))) (.node (.leaf (.ubHLePi 5 1 0 17988)) (.leaf (.ubHGe0 6 0 6 1308))))
            (.node (.node (.leaf (.ubHGe0 6 1 5 7267)) (.leaf (.ubHGe0 6 2 4 9141))) (.node (.leaf (.ubHGe0 6 3 3 4501)) (.leaf (.ubHGe0 6 4 2 870))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 6 5 1 59)) (.leaf (.ubHGe0 6 6 0 1))) (.node (.leaf (.ubHLePi 6 0 5 14511)) (.leaf (.ubHLePi 6 1 4 51329))))
            (.node (.node (.leaf (.ubHLePi 6 2 3 47016)) (.leaf (.ubHLePi 6 3 2 15908))) (.node (.leaf (.ubHLePi 6 4 1 1890)) (.leaf (.ubHLePi 6 5 0 58)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 6 0 4 58994)) (.leaf (.ubHGe0 6 1 3 141184))) (.node (.leaf (.ubHGe0 6 2 2 88944)) (.leaf (.ubHGe0 6 3 1 18512))))
            (.node (.node (.leaf (.ubHGe0 6 4 0 1020)) (.leaf (.ubHLePi 6 0 3 119552))) (.node (.leaf (.ubHLePi 6 1 2 189699)) (.leaf (.ubHLePi 6 2 1 73551)))))))))
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 6 3 0 7105)) (.node (.leaf (.ubHGe0 6 0 2 130446)) (.leaf (.ubHGe0 6 1 1 124890))))
            (.node (.node (.leaf (.ubHGe0 6 2 0 22482)) (.leaf (.ubHLePi 6 0 1 73523))) (.node (.leaf (.ubHLePi 6 1 0 32313)) (.leaf (.ubHGe0 6 0 0 16837)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 7 0 6 773)) (.leaf (.ubHLePi 7 1 5 4032))) (.node (.leaf (.ubHLePi 7 2 4 3859)) (.leaf (.ubHLePi 7 3 3 904))))
            (.node (.node (.leaf (.ubHGe0 7 4 2 172)) (.leaf (.ubHGe0 7 5 1 58))) (.node (.leaf (.ubHGe0 7 6 0 7)) (.leaf (.ubHGe0 7 0 5 8155))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 7 1 4 25626)) (.leaf (.ubHGe0 7 2 3 16686))) (.node (.leaf (.ubHGe0 7 3 2 1880)) (.leaf (.ubHLePi 7 4 1 585))))
            (.node (.node (.leaf (.ubHLePi 7 5 0 82)) (.leaf (.ubHLePi 7 0 4 31040))) (.node (.leaf (.ubHLePi 7 1 3 62849)) (.leaf (.ubHLePi 7 2 2 25794)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 7 3 1 675)) (.leaf (.ubHGe0 7 4 0 451))) (.node (.leaf (.ubHGe0 7 0 3 58304)) (.leaf (.ubHGe0 7 1 2 74479))))
            (.node (.node (.leaf (.ubHGe0 7 2 1 16660)) (.leaf (.ubHLePi 7 3 0 339))) (.node (.leaf (.ubHLePi 7 0 2 58461)) (.leaf (.ubHLePi 7 1 1 42619)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 7 2 0 3670)) (.node (.leaf (.ubHGe0 7 0 1 30013)) (.leaf (.ubHGe0 7 1 0 9388))))
            (.node (.node (.leaf (.ubHLePi 7 0 0 6197)) (.leaf (.ubHLePi 8 0 6 331))) (.node (.leaf (.ubHLePi 8 1 5 2142)) (.leaf (.ubHLePi 8 2 4 4580)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 8 3 3 4001)) (.leaf (.ubHLePi 8 4 2 1222))) (.node (.leaf (.ubHLePi 8 5 1 9)) (.leaf (.ubHGe0 8 6 0 37))))
            (.node (.node (.leaf (.ubHGe0 8 0 5 3837)) (.leaf (.ubHGe0 8 1 4 18676))) (.node (.leaf (.ubHGe0 8 2 3 28563)) (.leaf (.ubHGe0 8 3 2 15964))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 8 4 1 2477)) (.leaf (.ubHLePi 8 5 0 141))) (.node (.leaf (.ubHLePi 8 0 4 17784)) (.leaf (.ubHLePi 8 1 3 62197))))
            (.node (.node (.leaf (.ubHLePi 8 2 2 63125)) (.leaf (.ubHLePi 8 3 1 19958))) (.node (.leaf (.ubHLePi 8 4 0 971)) (.leaf (.ubHGe0 8 0 3 41983)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 8 1 2 98718)) (.leaf (.ubHGe0 8 2 1 58901))) (.node (.leaf (.ubHGe0 8 3 0 7692)) (.leaf (.ubHLePi 8 0 2 53255))))
            (.node (.node (.leaf (.ubHLePi 8 1 1 74851)) (.leaf (.ubHLePi 8 2 0 19569))) (.node (.leaf (.ubHGe0 8 0 1 34499)) (.leaf (.ubHGe0 8 1 0 21730))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 8 0 0 8939)) (.node (.leaf (.ubHLePi 9 0 6 53)) (.leaf (.ubHLePi 9 1 5 848))))
            (.node (.node (.leaf (.ubHLePi 9 2 4 4409)) (.leaf (.ubHLePi 9 3 3 6938))) (.node (.leaf (.ubHLePi 9 4 2 4197)) (.leaf (.ubHLePi 9 5 1 941)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 9 6 0 74)) (.leaf (.ubHGe0 9 0 5 1004))) (.node (.leaf (.ubHGe0 9 1 4 12081)) (.leaf (.ubHGe0 9 2 3 35670))))
            (.node (.node (.leaf (.ubHGe0 9 3 2 34862)) (.leaf (.ubHGe0 9 4 1 12147))) (.node (.leaf (.ubHGe0 9 5 0 1271)) (.leaf (.ubHLePi 9 0 4 7842))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 9 1 3 55774)) (.leaf (.ubHLePi 9 2 2 98656))) (.node (.leaf (.ubHLePi 9 3 1 55148)) (.leaf (.ubHLePi 9 4 0 8607))))
            (.node (.node (.leaf (.ubHGe0 9 0 3 27098)) (.leaf (.ubHGe0 9 1 2 113865))) (.node (.leaf (.ubHGe0 9 2 1 113272)) (.leaf (.ubHGe0 9 3 0 27952)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 9 0 2 45837)) (.leaf (.ubHLePi 9 1 1 106827))) (.node (.leaf (.ubHLePi 9 2 0 46345)) (.leaf (.ubHGe0 9 0 1 37462))))
            (.node (.node (.leaf (.ubHGe0 9 1 0 37667)) (.leaf (.ubHLePi 9 0 0 11856))) (.node (.leaf (.ubHGe0 10 0 6 275)) (.leaf (.ubHGe0 10 1 5 1785)))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 10 2 4 3503)) (.leaf (.ubHGe0 10 3 3 4368))) (.node (.leaf (.ubHGe0 10 4 2 2979)) (.leaf (.ubHGe0 10 5 1 927))))
            (.node (.node (.leaf (.ubHGe0 10 6 0 205)) (.leaf (.ubHLePi 10 0 5 3090))) (.node (.leaf (.ubHLePi 10 1 4 14402)) (.leaf (.ubHLePi 10 2 3 24706)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 10 3 2 22800)) (.leaf (.ubHLePi 10 4 1 9636))) (.node (.leaf (.ubHLePi 10 5 0 1903)) (.leaf (.ubHGe0 10 0 4 13619))))
            (.node (.node (.leaf (.ubHGe0 10 1 3 49013)) (.leaf (.ubHGe0 10 2 2 65479))) (.node (.leaf (.ubHGe0 10 3 1 38641)) (.leaf (.ubHGe0 10 4 0 8690))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 10 0 3 31791)) (.leaf (.ubHLePi 10 1 2 85627))) (.node (.leaf (.ubHLePi 10 2 1 76132)) (.leaf (.ubHLePi 10 3 0 22535))))
            (.node (.node (.leaf (.ubHGe0 10 0 2 42020)) (.leaf (.ubHGe0 10 1 1 75224))) (.node (.leaf (.ubHGe0 10 2 0 33385)) (.leaf (.ubHLePi 10 0 1 29756)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 10 1 0 26537)) (.leaf (.ubHLePi 11 0 6 190))) (.node (.leaf (.ubHLePi 11 1 5 3657)) (.leaf (.ubHLePi 11 2 4 11529))))
            (.node (.node (.leaf (.ubHLePi 11 3 3 12723)) (.leaf (.ubHLePi 11 4 2 3168))) (.node (.leaf (.ubHGe0 11 5 1 1349)) (.leaf (.ubHGe0 11 6 0 428))))))))))
      (.node
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHGe0 11 0 5 4542)) (.node (.leaf (.ubHGe0 11 1 4 38406)) (.leaf (.ubHGe0 11 2 3 78654))))
            (.node (.node (.leaf (.ubHGe0 11 3 2 48014)) (.leaf (.ubHGe0 11 4 1 193))) (.node (.leaf (.ubHLePi 11 5 0 3512)) (.leaf (.ubHLePi 11 0 4 28688)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 11 1 3 145498)) (.leaf (.ubHLePi 11 2 2 178802))) (.node (.leaf (.ubHLePi 11 3 1 46727)) (.leaf (.ubHGe0 11 4 0 7628))))
            (.node (.node (.leaf (.ubHGe0 11 0 3 81613)) (.leaf (.ubHGe0 11 1 2 249316))) (.node (.leaf (.ubHGe0 11 2 1 157623)) (.leaf (.ubHGe0 11 3 0 5996))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 11 0 2 116693)) (.leaf (.ubHLePi 11 1 1 192846))) (.node (.leaf (.ubHLePi 11 2 0 42316)) (.leaf (.ubHGe0 11 0 1 80879))))
            (.node (.node (.leaf (.ubHGe0 11 1 0 52970)) (.leaf (.ubHLePi 11 0 0 21265))) (.node (.leaf (.ubHLePi 12 0 6 70)) (.leaf (.ubHLePi 12 1 5 751)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 12 2 4 2375)) (.leaf (.ubHLePi 12 3 3 2727))) (.node (.leaf (.ubHLePi 12 4 2 836)) (.leaf (.ubHGe0 12 5 1 462))))
            (.node (.node (.leaf (.ubHGe0 12 6 0 258)) (.leaf (.ubHGe0 12 0 5 1081))) (.node (.leaf (.ubHGe0 12 1 4 7808)) (.leaf (.ubHGe0 12 2 3 16201)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHGe0 12 3 2 10481)) (.node (.leaf (.ubHLePi 12 4 1 629)) (.leaf (.ubHLePi 12 5 0 1794))))
            (.node (.node (.leaf (.ubHLePi 12 0 4 6106)) (.leaf (.ubHLePi 12 1 3 29380))) (.node (.leaf (.ubHLePi 12 2 2 36851)) (.leaf (.ubHLePi 12 3 1 8376)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 12 4 0 4377)) (.leaf (.ubHGe0 12 0 3 16660))) (.node (.leaf (.ubHGe0 12 1 2 50058)) (.leaf (.ubHGe0 12 2 1 30434))))
            (.node (.node (.leaf (.ubHLePi 12 3 0 2824)) (.leaf (.ubHLePi 12 0 2 23340))) (.node (.leaf (.ubHLePi 12 1 1 37489)) (.leaf (.ubHLePi 12 2 0 5088))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 12 0 1 15770)) (.leaf (.ubHGe0 12 1 0 8912))) (.node (.leaf (.ubHLePi 12 0 0 3867)) (.leaf (.ubHGe0 13 0 6 25))))
            (.node (.node (.leaf (.ubHGe0 13 1 5 438)) (.leaf (.ubHGe0 13 2 4 1817))) (.node (.leaf (.ubHGe0 13 3 3 2507)) (.leaf (.ubHGe0 13 4 2 1011)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 13 5 1 110)) (.leaf (.ubHLePi 13 6 0 1135))) (.node (.leaf (.ubHLePi 13 0 5 542)) (.leaf (.ubHLePi 13 1 4 5322))))
            (.node (.node (.leaf (.ubHLePi 13 2 3 13588)) (.leaf (.ubHLePi 13 3 2 10834))) (.node (.leaf (.ubHLePi 13 4 1 1639)) (.leaf (.ubHGe0 13 5 0 5896))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHGe0 13 0 4 3702)) (.node (.leaf (.ubHGe0 13 1 3 22381)) (.leaf (.ubHGe0 13 2 2 34178))))
            (.node (.node (.leaf (.ubHGe0 13 3 1 13681)) (.leaf (.ubHLePi 13 4 0 11947))) (.node (.leaf (.ubHLePi 13 0 3 11512)) (.leaf (.ubHLePi 13 1 2 42184)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 13 2 1 34620)) (.leaf (.ubHGe0 13 3 0 9478))) (.node (.leaf (.ubHGe0 13 0 2 17961)) (.leaf (.ubHGe0 13 1 1 36279))))
            (.node (.node (.leaf (.ubHGe0 13 2 0 2238)) (.leaf (.ubHLePi 13 0 1 13637))) (.node (.leaf (.ubHLePi 13 1 0 7977)) (.leaf (.ubHGe0 13 0 0 3452))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 14 0 6 7)) (.leaf (.ubHLePi 14 1 5 258))) (.node (.leaf (.ubHLePi 14 2 4 2328)) (.leaf (.ubHLePi 14 3 3 7002))))
            (.node (.node (.leaf (.ubHLePi 14 4 2 6840)) (.leaf (.ubHLePi 14 5 1 598))) (.node (.leaf (.ubHLePi 14 6 0 92)) (.leaf (.ubHGe0 14 0 5 279)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 14 1 4 5537)) (.leaf (.ubHGe0 14 2 3 28266))) (.node (.leaf (.ubHGe0 14 3 2 45349)) (.leaf (.ubHGe0 14 4 1 16004))))
            (.node (.node (.leaf (.ubHGe0 14 5 0 1095)) (.leaf (.ubHLePi 14 0 4 3243))) (.node (.leaf (.ubHLePi 14 1 3 36832)) (.leaf (.ubHLePi 14 2 2 103720)))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 14 3 1 73385)) (.leaf (.ubHLePi 14 4 0 10283))) (.node (.leaf (.ubHGe0 14 0 3 15604)) (.leaf (.ubHGe0 14 1 2 99810))))
            (.node (.node (.leaf (.ubHGe0 14 2 1 134946)) (.leaf (.ubHGe0 14 3 0 36386))) (.node (.leaf (.ubHLePi 14 0 2 34620)) (.leaf (.ubHLePi 14 1 1 111210)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 14 2 0 58080)) (.leaf (.ubHGe0 14 0 1 34249))) (.node (.leaf (.ubHGe0 14 1 0 43287)) (.leaf (.ubHLePi 14 0 0 12314))))
            (.node (.node (.leaf (.ubHLePi 15 0 6 1)) (.leaf (.ubHLePi 15 1 5 68))) (.node (.leaf (.ubHLePi 15 2 4 983)) (.leaf (.ubHLePi 15 3 3 5523))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 15 4 2 13870)) (.leaf (.ubHLePi 15 5 1 14948))) (.node (.leaf (.ubHLePi 15 6 0 6130)) (.leaf (.ubHGe0 15 0 5 68))))
            (.node (.node (.leaf (.ubHGe0 15 1 4 2137)) (.leaf (.ubHGe0 15 2 3 19102))) (.node (.leaf (.ubHGe0 15 3 2 67120)) (.leaf (.ubHGe0 15 4 1 95249)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 15 5 0 47850)) (.leaf (.ubHLePi 15 0 4 1154))) (.node (.leaf (.ubHLePi 15 1 3 21880)) (.leaf (.ubHLePi 15 2 2 121109))))
            (.node (.node (.leaf (.ubHLePi 15 3 1 240854)) (.leaf (.ubHLePi 15 4 0 155833))) (.node (.leaf (.ubHGe0 15 0 3 8300)) (.leaf (.ubHGe0 15 1 2 96507)))))))))
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHGe0 15 2 1 302126)) (.node (.leaf (.ubHGe0 15 3 0 269956)) (.leaf (.ubHLePi 15 0 2 28648))))
            (.node (.node (.leaf (.ubHLePi 15 1 1 188014)) (.leaf (.ubHLePi 15 2 0 261764))) (.node (.leaf (.ubHGe0 15 0 1 46441)) (.leaf (.ubHGe0 15 1 0 134532)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 15 0 0 28611)) (.leaf (.ubHLePi 16 1 5 7))) (.node (.leaf (.ubHLePi 16 2 4 187)) (.leaf (.ubHLePi 16 3 3 1549))))
            (.node (.node (.leaf (.ubHLePi 16 4 2 4909)) (.leaf (.ubHLePi 16 5 1 5633))) (.node (.leaf (.ubHLePi 16 6 0 3410)) (.leaf (.ubHGe0 16 0 5 6))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 16 1 4 371)) (.leaf (.ubHGe0 16 2 3 4980))) (.node (.leaf (.ubHGe0 16 3 2 22558)) (.leaf (.ubHGe0 16 4 1 35392))))
            (.node (.node (.leaf (.ubHGe0 16 5 0 24099)) (.leaf (.ubHLePi 16 0 4 184))) (.node (.leaf (.ubHLePi 16 1 3 5311)) (.leaf (.ubHLePi 16 2 2 38540)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 16 3 1 87336)) (.leaf (.ubHLePi 16 4 0 72577))) (.node (.leaf (.ubHGe0 16 0 3 1880)) (.leaf (.ubHGe0 16 1 2 29042))))
            (.node (.node (.leaf (.ubHGe0 16 2 1 106146)) (.leaf (.ubHGe0 16 3 0 117920))) (.node (.leaf (.ubHLePi 16 0 2 8151)) (.leaf (.ubHLePi 16 1 1 63688)))))))
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 16 2 0 108209)) (.node (.leaf (.ubHGe0 16 0 1 15119)) (.leaf (.ubHGe0 16 1 0 52924))))
            (.node (.node (.leaf (.ubHLePi 16 0 0 10748)) (.leaf (.ubHGe0 17 2 4 9))) (.node (.leaf (.ubHGe0 17 3 3 136)) (.leaf (.ubHGe0 17 4 2 183)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 17 5 1 792)) (.leaf (.ubHLePi 17 6 0 1106))) (.node (.leaf (.ubHLePi 17 1 4 15)) (.leaf (.ubHLePi 17 2 3 386))))
            (.node (.node (.leaf (.ubHLePi 17 3 2 958)) (.leaf (.ubHGe0 17 4 1 3587))) (.node (.leaf (.ubHGe0 17 5 0 6886)) (.leaf (.ubHGe0 17 0 4 7))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 17 1 3 370)) (.leaf (.ubHGe0 17 2 2 1750))) (.node (.leaf (.ubHLePi 17 3 1 6248)) (.leaf (.ubHLePi 17 4 0 17856))))
            (.node (.node (.leaf (.ubHLePi 17 0 3 119)) (.leaf (.ubHLePi 17 1 2 1363))) (.node (.leaf (.ubHGe0 17 2 1 5173)) (.leaf (.ubHGe0 17 3 0 24536)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 17 0 2 387)) (.leaf (.ubHLePi 17 1 1 1985))) (.node (.leaf (.ubHLePi 17 2 0 18788)) (.leaf (.ubHGe0 17 0 1 265))))
            (.node (.node (.leaf (.ubHGe0 17 1 0 7588)) (.leaf (.ubHLePi 17 0 0 1261))) (.node (.leaf (.ubHGe0 18 3 3 158)) (.leaf (.ubHLePi 18 4 2 209))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.leaf (.ubHLePi 18 5 1 4530)) (.node (.leaf (.ubHGe0 18 6 0 4547)) (.leaf (.ubHLePi 18 2 3 443))))
            (.node (.node (.leaf (.ubHGe0 18 3 2 276)) (.leaf (.ubHGe0 18 4 1 21167))) (.node (.leaf (.ubHLePi 18 5 0 20952)) (.leaf (.ubHGe0 18 1 3 415)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 18 2 2 313)) (.leaf (.ubHLePi 18 3 1 39281))) (.node (.leaf (.ubHGe0 18 4 0 38792)) (.leaf (.ubHLePi 18 0 3 130))))
            (.node (.node (.leaf (.ubHLePi 18 1 2 631)) (.leaf (.ubHGe0 18 2 1 36166))) (.node (.leaf (.ubHLePi 18 3 0 36145)) (.leaf (.ubHGe0 18 0 2 251))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 18 1 1 16502)) (.leaf (.ubHGe0 18 2 0 17080))) (.node (.leaf (.ubHGe0 18 0 1 2980)) (.leaf (.ubHLePi 18 1 0 3405))))
            (.node (.node (.leaf (.ubHGe0 19 4 2 786)) (.leaf (.ubHGe0 19 5 1 6218))) (.node (.leaf (.ubHGe0 19 6 0 13701)) (.leaf (.ubHLePi 19 3 2 2902)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 19 4 1 30186)) (.leaf (.ubHLePi 19 5 0 81940))) (.node (.leaf (.ubHGe0 19 2 2 4043)) (.leaf (.ubHGe0 19 3 1 58835))))
            (.node (.node (.leaf (.ubHGe0 19 4 0 204884)) (.leaf (.ubHLePi 19 1 2 2516))) (.node (.leaf (.ubHLePi 19 2 1 57505)) (.leaf (.ubHLePi 19 3 0 273998)))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 19 0 2 590)) (.leaf (.ubHGe0 19 1 1 28170))) (.node (.leaf (.ubHGe0 19 2 0 206597)) (.leaf (.ubHLePi 19 0 1 5531))))
            (.node (.node (.leaf (.ubHLePi 19 1 0 83241)) (.leaf (.ubHGe0 19 0 0 13997))) (.node (.leaf (.ubHGe0 20 5 1 1042)) (.leaf (.ubHGe0 20 6 0 13099)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 20 4 1 4298)) (.leaf (.ubHLePi 20 5 0 73257))) (.node (.leaf (.ubHGe0 20 3 1 7201)) (.leaf (.ubHGe0 20 4 0 171408))))
            (.node (.node (.leaf (.ubHLePi 20 2 1 6107)) (.leaf (.ubHLePi 20 3 0 214691))) (.node (.leaf (.ubHGe0 20 1 1 2616)) (.leaf (.ubHGe0 20 2 0 151760))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 20 0 1 452)) (.leaf (.ubHLePi 20 1 0 57385))) (.node (.leaf (.ubHGe0 20 0 0 9065)) (.leaf (.ubHLePi 21 6 0 8102))))
            (.node (.node (.leaf (.ubHGe0 21 5 0 45651)) (.leaf (.ubHLePi 21 4 0 107538))) (.node (.leaf (.ubHGe0 21 3 0 135528)) (.leaf (.ubHLePi 21 2 0 96352)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 21 1 0 36629)) (.leaf (.ubHLePi 21 0 0 5816))) (.node (.leaf (.ubPHi 6 262656)) (.leaf (.ubPHi 5 971944))))
            (.node (.node (.leaf (.ubPHi 4 3384415)) (.leaf (.ubPHi 3 2791042))) (.node (.leaf (.ubPHi 2 2960169)) (.leaf (.eqP0 (-176294)))))))))))))

lemma step2cScale_pos : 0 < step2cScale := by decide
lemma step2cLb_strict : (-843) * (step2cScale : ℤ) < 1330 * step2cLb := by decide
lemma step2cCert_u_ok :
    checkBinoBoundU 21 6 [(2, 1), (20, 1), (21, 0)] step2cCert 3 (-1) step2cScale step2cLb = true := by
  decide
private lemma step2cCert_c_0 : checkBinoCForJ 21 6 0 step2cCert = true := by decide
private lemma step2cCert_c_1 : checkBinoCForJ 21 6 1 step2cCert = true := by decide
private lemma step2cCert_c_2 : checkBinoCForJ 21 6 2 step2cCert = true := by decide
private lemma step2cCert_c_3 : checkBinoCForJ 21 6 3 step2cCert = true := by decide
private lemma step2cCert_c_4 : checkBinoCForJ 21 6 4 step2cCert = true := by decide
private lemma step2cCert_c_5 : checkBinoCForJ 21 6 5 step2cCert = true := by decide
private lemma step2cCert_c_6 : checkBinoCForJ 21 6 6 step2cCert = true := by decide
private lemma step2cCert_c_7 : checkBinoCForJ 21 6 7 step2cCert = true := by decide
private lemma step2cCert_c_8 : checkBinoCForJ 21 6 8 step2cCert = true := by decide
private lemma step2cCert_c_9 : checkBinoCForJ 21 6 9 step2cCert = true := by decide
private lemma step2cCert_c_10 : checkBinoCForJ 21 6 10 step2cCert = true := by decide
private lemma step2cCert_c_11 : checkBinoCForJ 21 6 11 step2cCert = true := by decide
private lemma step2cCert_c_12 : checkBinoCForJ 21 6 12 step2cCert = true := by decide
private lemma step2cCert_c_13 : checkBinoCForJ 21 6 13 step2cCert = true := by decide
private lemma step2cCert_c_14 : checkBinoCForJ 21 6 14 step2cCert = true := by decide
private lemma step2cCert_c_15 : checkBinoCForJ 21 6 15 step2cCert = true := by decide
private lemma step2cCert_c_16 : checkBinoCForJ 21 6 16 step2cCert = true := by decide
private lemma step2cCert_c_17 : checkBinoCForJ 21 6 17 step2cCert = true := by decide
private lemma step2cCert_c_18 : checkBinoCForJ 21 6 18 step2cCert = true := by decide
private lemma step2cCert_c_19 : checkBinoCForJ 21 6 19 step2cCert = true := by decide
private lemma step2cCert_c_20 : checkBinoCForJ 21 6 20 step2cCert = true := by decide
private lemma step2cCert_c_21 : checkBinoCForJ 21 6 21 step2cCert = true := by decide
lemma step2cCert_c_ok : ∀ j ≤ 21, checkBinoCForJ 21 6 j step2cCert = true := by
  intro j hj
  match j with
  | 0 => exact step2cCert_c_0
  | 1 => exact step2cCert_c_1
  | 2 => exact step2cCert_c_2
  | 3 => exact step2cCert_c_3
  | 4 => exact step2cCert_c_4
  | 5 => exact step2cCert_c_5
  | 6 => exact step2cCert_c_6
  | 7 => exact step2cCert_c_7
  | 8 => exact step2cCert_c_8
  | 9 => exact step2cCert_c_9
  | 10 => exact step2cCert_c_10
  | 11 => exact step2cCert_c_11
  | 12 => exact step2cCert_c_12
  | 13 => exact step2cCert_c_13
  | 14 => exact step2cCert_c_14
  | 15 => exact step2cCert_c_15
  | 16 => exact step2cCert_c_16
  | 17 => exact step2cCert_c_17
  | 18 => exact step2cCert_c_18
  | 19 => exact step2cCert_c_19
  | 20 => exact step2cCert_c_20
  | 21 => exact step2cCert_c_21
  | _ + 22 => omega

end DegreeSensitivity
