module

public import DegreeSensitivity.IntTrieVerifier

@[expose] public section

/-!
# New World Record: `B_9 ≤ 46` (Impossibility of `(n = 47, d = 9)`)

Small-integer Subset-`J` Terwilliger LP Farkas infeasibility certificate
(1077 pure integer multipliers, ≤ 20 digits, `J = [5, 6, 7, 8, 9, 10, 11, 12, 13, 17]`),
verified via `j`-sliced depth-8 `by decide` checks.
Strictly beats Wellens (2022) `B_9 ≤ 47`.
-/

namespace DegreeSensitivity

/-- Balanced binary tree of small-integer Farkas multipliers for `(n = 47, d = 9)`. -/
def cert_47_9 : BinTree BinoStep :=
  (.node
    (.node
      (.node
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.eqP0 (-624946579881897))) (.leaf (.eqP1 2107835670456198))) (.node (.leaf (.eqDiag 5 774744469027572)) (.leaf (.eqB00 5 (-10861405782980995)))))
            (.node (.node (.leaf (.eqB10 5 5269234726628599)) (.leaf (.eqB01 5 20592940218474624))) (.node (.leaf (.eqDiag 6 (-2106281728184752))) (.leaf (.eqB00 6 47427858739591373)))))
            (.node
            (.node (.node (.leaf (.eqB10 6 (-31551883082525790))) (.leaf (.eqB01 6 (-86776593489021169)))) (.node (.leaf (.eqDiag 7 3804933575704312)) (.leaf (.eqB00 7 (-85654742598248865)))))
            (.node (.node (.leaf (.eqB10 7 75222027267122422)) (.leaf (.eqB01 7 149500007066804847))) (.node (.leaf (.eqDiag 8 (-4945439050572909))) (.leaf (.eqB00 8 77417134956321579))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqB10 8 (-88640047520285522))) (.leaf (.eqB01 8 (-126593236816816498)))) (.node (.leaf (.eqDiag 9 4697895182216114)) (.leaf (.eqB00 9 (-49239452565843846)))))
            (.node (.node (.leaf (.eqB10 9 54444096114620547)) (.leaf (.eqB01 9 85409564236835939))) (.node (.leaf (.eqDiag 10 (-3169207092789264))) (.leaf (.eqB00 10 60386794594388269)))))
            (.node
            (.node (.node (.leaf (.eqB10 10 (-29220741871780333))) (.leaf (.eqB01 10 (-125699536181932334)))) (.node (.leaf (.eqDiag 11 1515829173256230)) (.leaf (.eqB00 11 (-78097054714128372)))))
            (.node
            (.node (.leaf (.eqB10 11 35422602922316427)) (.leaf (.eqB01 11 158974467831289559)))
            (.node (.leaf (.eqDiag 12 (-455886709392868))) (.node (.leaf (.eqB00 12 52289739751286267)) (.leaf (.eqB10 12 (-31202057559600830)))))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.eqB01 12 (-99904100398669098))) (.leaf (.eqDiag 13 66872898391708))) (.node (.leaf (.eqB00 13 (-13795276592815237))) (.leaf (.eqB10 13 10193967761471566))))
            (.node (.node (.leaf (.eqB01 13 24750933173928225)) (.leaf (.eqDiag 17 (-127167836482)))) (.node (.leaf (.eqB00 17 56481132429448)) (.leaf (.eqB10 17 (-51630729287736))))))
            (.node
            (.node (.node (.leaf (.eqB01 17 (-73231784324424))) (.leaf (.eqSym 5 6 0 296549221823367331))) (.node (.leaf (.eqSym 5 6 1 (-257472544320946516))) (.leaf (.eqSym 5 6 2 1989860467830648601))))
            (.node
            (.node (.leaf (.eqSym 5 6 3 (-897848692151226409))) (.leaf (.eqSym 5 6 4 315053718077926203)))
            (.node (.leaf (.eqSym 5 6 5 (-50258815494424045))) (.node (.leaf (.eqSym 5 7 0 (-326612183819561942))) (.leaf (.eqSym 5 7 1 (-92356820556240730))))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 5 7 2 (-4827442967999181236))) (.leaf (.eqSym 5 7 4 159515833808475153))) (.node (.leaf (.eqSym 5 7 5 21723357242113611)) (.leaf (.eqSym 5 8 0 (-523885863438824028)))))
            (.node (.node (.leaf (.eqSym 5 8 1 2034074295107767013)) (.leaf (.eqSym 5 8 2 2729827480294981458))) (.node (.leaf (.eqSym 5 8 3 5025311943275917312)) (.leaf (.eqSym 5 8 4 (-1708225430437894653))))))
            (.node
            (.node (.node (.leaf (.eqSym 5 9 1 (-764649456325593554))) (.leaf (.eqSym 5 9 2 (-3281697354928257613)))) (.node (.leaf (.eqSym 5 9 3 (-2360152236939037914))) (.leaf (.eqSym 5 9 5 350760285079529650))))
            (.node
            (.node (.leaf (.eqSym 5 10 0 2324520328204355450)) (.leaf (.eqSym 5 10 1 (-3212416572914666936))))
            (.node (.leaf (.eqSym 5 10 2 8396538034645492642)) (.node (.leaf (.eqSym 5 10 3 (-4419778621137989436))) (.leaf (.eqSym 5 10 5 623565245056470109)))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 5 11 0 (-2400542002287847826))) (.leaf (.eqSym 5 11 3 (-6466188022714098315)))) (.node (.leaf (.eqSym 5 11 4 9477591083123613472)) (.leaf (.eqSym 5 11 5 (-3554572553593809717)))))
            (.node (.node (.leaf (.eqSym 5 12 0 353629307646314952)) (.leaf (.eqSym 5 12 1 5354800115944140278))) (.node (.leaf (.eqSym 5 12 2 (-11544624124264797944))) (.leaf (.eqSym 5 12 3 17786402183806104410)))))
            (.node
            (.node (.node (.leaf (.eqSym 5 12 4 (-14147606388764767441))) (.leaf (.eqSym 5 12 5 4195314037678844562))) (.node (.leaf (.eqSym 5 13 0 304259403499713624)) (.leaf (.eqSym 5 13 1 (-3159128804821708280)))))
            (.node (.node (.leaf (.eqSym 5 13 2 6754744622656576286)) (.leaf (.eqSym 5 13 3 (-8916693026992917067)))) (.node (.leaf (.eqSym 5 13 4 6045184152354063833)) (.leaf (.eqSym 5 13 5 (-1618847572997351239)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 5 17 0 (-18885388849989481))) (.leaf (.eqSym 5 17 1 102451541471535865))) (.node (.leaf (.eqSym 5 17 2 (-217177204872975251))) (.leaf (.eqSym 5 17 3 248949074899651417))))
            (.node (.node (.leaf (.eqSym 5 17 4 (-141893738590864941))) (.leaf (.eqSym 5 17 5 33049307771114410))) (.node (.leaf (.eqSym 6 7 0 (-372427198516437571))) (.leaf (.eqSym 6 7 1 2065677245047957337)))))
            (.node
            (.node (.node (.leaf (.eqSym 6 7 3 20846135609015704901)) (.leaf (.eqSym 6 7 4 (-16714828408124882814)))) (.node (.leaf (.eqSym 6 7 5 7071675127961891488)) (.leaf (.eqSym 6 7 6 (-1344769809583650448)))))
            (.node
            (.node (.leaf (.eqSym 6 8 0 1396371935190215354)) (.leaf (.eqSym 6 8 1 34086294904266982)))
            (.node (.leaf (.eqSym 6 8 2 (-4664541782201831946))) (.node (.leaf (.eqSym 6 8 3 (-39367716464884436809))) (.leaf (.eqSym 6 8 4 26992419409040291872))))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 6 8 5 (-11379189894712541935))) (.leaf (.eqSym 6 8 6 2496215368695297229))) (.node (.leaf (.eqSym 6 9 0 1985528047504532038)) (.leaf (.eqSym 6 9 1 (-13682646022108006360)))))
            (.node (.node (.leaf (.eqSym 6 9 2 34006544029543897771)) (.leaf (.eqSym 6 9 3 (-5744167538722643193)))) (.node (.leaf (.eqSym 6 9 4 8917572353037642616)) (.leaf (.eqSym 6 9 5 (-2424200559934949796))))))
            (.node
            (.node (.node (.leaf (.eqSym 6 9 6 (-345952122520400913))) (.leaf (.eqSym 6 10 0 (-6465146240923499979)))) (.node (.leaf (.eqSym 6 10 1 9639598467132744222)) (.leaf (.eqSym 6 10 2 (-22269411741994288260)))))
            (.node
            (.node (.leaf (.eqSym 6 10 3 7715924775976372075)) (.leaf (.eqSym 6 10 4 2198061551396031548)))
            (.node (.leaf (.eqSym 6 10 5 (-2368589851690603424))) (.node (.leaf (.eqSym 6 10 6 (-66878653468650455))) (.leaf (.eqSym 6 11 0 6926575619252138787)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 6 11 1 3596900281054639834)) (.leaf (.eqSym 6 11 2 (-12708368078922163959)))) (.node (.leaf (.eqSym 6 11 3 38030316054433631371)) (.leaf (.eqSym 6 11 4 (-48385562736805844062)))))
            (.node (.node (.leaf (.eqSym 6 11 5 18764463944537399381)) (.leaf (.eqSym 6 11 6 (-901429372966690149)))) (.node (.leaf (.eqSym 6 12 0 (-5817065226068185865))) (.leaf (.eqSym 6 12 1 7200182134814216132)))))
            (.node
            (.node (.node (.leaf (.eqSym 6 12 2 (-13423538813955937491))) (.leaf (.eqSym 6 12 4 13520809696936212346))) (.node (.leaf (.eqSym 6 12 5 (-2983820808771241989))) (.leaf (.eqSym 6 12 6 (-1702977816203292440)))))
            (.node
            (.node (.leaf (.eqSym 6 13 0 2757861267726195901)) (.leaf (.eqSym 6 13 1 (-10039206740572680937))))
            (.node (.leaf (.eqSym 6 13 2 23265189943145082058)) (.node (.leaf (.eqSym 6 13 3 (-25291640861746138123))) (.leaf (.eqSym 6 13 4 15995643657148358629))))))))))
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 6 13 5 (-7650310792934544184))) (.leaf (.eqSym 6 13 6 2029470614188350854))) (.node (.leaf (.eqSym 6 17 0 (-154484398129986901))) (.leaf (.eqSym 6 17 1 896313999976217572))))
            (.node (.node (.leaf (.eqSym 6 17 2 (-2215992524719118373))) (.leaf (.eqSym 6 17 3 2913234881879881765))) (.node (.leaf (.eqSym 6 17 4 (-2208861390472746850))) (.leaf (.eqSym 6 17 5 919758497425837372)))))
            (.node
            (.node (.node (.leaf (.eqSym 6 17 6 (-165787370711014266))) (.leaf (.eqSym 7 8 1 (-12248090750110310307)))) (.node (.leaf (.eqSym 7 8 2 18565389539364115947)) (.leaf (.eqSym 7 8 3 30454585012427943558))))
            (.node (.node (.leaf (.eqSym 7 8 4 (-11494371702916544970))) (.leaf (.eqSym 7 8 6 2648465233561364175))) (.node (.leaf (.eqSym 7 8 7 (-1079855789889385415))) (.leaf (.eqSym 7 9 0 (-3217557073574750489)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 7 9 1 28351405149105881928)) (.leaf (.eqSym 7 9 2 (-48960982562779842633)))) (.node (.leaf (.eqSym 7 9 4 (-14972510927658432464))) (.leaf (.eqSym 7 9 5 3461918247017456910))))
            (.node (.node (.leaf (.eqSym 7 9 6 676568492610971696)) (.leaf (.eqSym 7 10 0 5772298774175793189))) (.node (.leaf (.eqSym 7 10 1 (-6850988396659556530))) (.leaf (.eqSym 7 10 2 13800146959243822547)))))
            (.node
            (.node (.node (.leaf (.eqSym 7 10 3 963887763276554731)) (.leaf (.eqSym 7 10 5 2298998905019302296))) (.node (.leaf (.eqSym 7 11 0 (-9926560933686921688))) (.leaf (.eqSym 7 11 5 32296164955070879668))))
            (.node
            (.node (.leaf (.eqSym 7 11 6 (-28437289812311828963))) (.leaf (.eqSym 7 11 7 6510892455181522389)))
            (.node (.leaf (.eqSym 7 12 0 10120905616650313849)) (.node (.leaf (.eqSym 7 12 1 (-9517124246686504917))) (.leaf (.eqSym 7 12 2 (-4385739666894385094)))))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 7 12 3 42890894661228833587)) (.leaf (.eqSym 7 12 4 (-55072942113314168335)))) (.node (.leaf (.eqSym 7 12 6 19373908253306534537)) (.leaf (.eqSym 7 12 7 (-5861725610740353043)))))
            (.node (.node (.leaf (.eqSym 7 13 0 (-3197732667362265567))) (.leaf (.eqSym 7 13 1 445252152779145686))) (.node (.leaf (.eqSym 7 13 2 22999427162934172589)) (.leaf (.eqSym 7 13 3 (-66496365265439697290))))))
            (.node
            (.node (.node (.leaf (.eqSym 7 13 4 79161336631736681767)) (.leaf (.eqSym 7 13 5 (-39878925804395390350)))) (.node (.leaf (.eqSym 7 13 6 7428243367806520439)) (.leaf (.eqSym 7 17 0 (-186552867235991050)))))
            (.node
            (.node (.leaf (.eqSym 7 17 1 1868034032558199398)) (.leaf (.eqSym 7 17 2 (-6845684399867064591))))
            (.node (.leaf (.eqSym 7 17 3 13033133437522070315)) (.node (.leaf (.eqSym 7 17 4 (-14176829699519424079))) (.leaf (.eqSym 7 17 5 8915306314749052739)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 7 17 6 (-3034664167459878262))) (.leaf (.eqSym 7 17 7 434495684134142675))) (.node (.leaf (.eqSym 8 9 0 581946727486726192)) (.leaf (.eqSym 8 9 1 (-16997788410495672972)))))
            (.node (.node (.leaf (.eqSym 8 9 2 24741587985986069394)) (.leaf (.eqSym 8 9 4 18100899541205984639))) (.node (.leaf (.eqSym 8 9 5 (-518934317396983210))) (.leaf (.eqSym 8 9 6 (-4537331653420681218))))))
            (.node
            (.node (.node (.leaf (.eqSym 8 9 7 1689395958373929779)) (.leaf (.eqSym 8 9 8 (-133510856234618908)))) (.node (.leaf (.eqSym 8 10 4 (-13771056862082465913))) (.leaf (.eqSym 8 11 0 4851930931886830303))))
            (.node
            (.node (.leaf (.eqSym 8 11 1 4158691154363070771)) (.leaf (.eqSym 8 11 2 (-9558265723897679663))))
            (.node (.leaf (.eqSym 8 11 5 (-11498742152275137592))) (.node (.leaf (.eqSym 8 11 7 12637146254435586519)) (.leaf (.eqSym 8 11 8 (-5201611896089064016))))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 8 12 0 (-7928096034198249842))) (.leaf (.eqSym 8 12 1 8620622605388753616))) (.node (.leaf (.eqSym 8 12 2 (-4203787498638585445))) (.leaf (.eqSym 8 12 4 6543765993880355471))))
            (.node (.node (.leaf (.eqSym 8 12 6 27101307053107887012)) (.leaf (.eqSym 8 12 7 (-33482460908309367800)))) (.node (.leaf (.eqSym 8 12 8 10716843272920354406)) (.leaf (.eqSym 8 13 0 3560719115495751641)))))
            (.node
            (.node (.node (.leaf (.eqSym 8 13 1 (-7797065036336084850))) (.leaf (.eqSym 8 13 2 11884430403056975485))) (.node (.leaf (.eqSym 8 13 3 (-17048839566142524759))) (.leaf (.eqSym 8 13 4 20086390760137657993))))
            (.node
            (.node (.leaf (.eqSym 8 13 5 (-13006787437047570237))) (.leaf (.eqSym 8 13 6 (-11316198443041052741))))
            (.node (.leaf (.eqSym 8 13 7 16818934955163289095)) (.node (.leaf (.eqSym 8 13 8 (-5337748484351091383))) (.leaf (.eqSym 8 17 0 (-242822136193258416))))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 8 17 1 1746969479461371600)) (.leaf (.eqSym 8 17 2 (-6233290996511125023)))) (.node (.leaf (.eqSym 8 17 3 13161022998396604547)) (.leaf (.eqSym 8 17 4 (-17170177157455679942)))))
            (.node (.node (.leaf (.eqSym 8 17 5 13645273526972941225)) (.leaf (.eqSym 8 17 6 (-6103102433912024655)))) (.node (.leaf (.eqSym 8 17 7 1257126627288379444)) (.leaf (.eqSym 8 17 8 (-48916580370860587))))))
            (.node
            (.node (.node (.leaf (.eqSym 9 10 0 (-2925706005587646888))) (.leaf (.eqSym 9 10 4 8227226451399023254))) (.node (.leaf (.eqSym 9 10 5 3044866008928112297)) (.leaf (.eqSym 9 10 8 218091365767668801))))
            (.node
            (.node (.leaf (.eqSym 9 10 9 (-64914306818195724))) (.leaf (.eqSym 9 11 0 3101821448014601781)))
            (.node (.leaf (.eqSym 9 11 1 (-4190354888777563936))) (.node (.leaf (.eqSym 9 11 2 7001111430492211360)) (.leaf (.eqSym 9 11 3 (-2535600489144817573)))))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 9 11 4 (-6473136206223640646))) (.leaf (.eqSym 9 11 6 9996987585765391018))) (.node (.leaf (.eqSym 9 11 7 (-12835858279232534570))) (.leaf (.eqSym 9 11 8 1534008738650606214))))
            (.node (.node (.leaf (.eqSym 9 11 9 1126320432231646245)) (.leaf (.eqSym 9 12 0 (-427122234946627928)))) (.node (.leaf (.eqSym 9 12 3 (-1637180158586055040))) (.leaf (.eqSym 9 12 5 7506931942761265475)))))
            (.node
            (.node (.node (.leaf (.eqSym 9 12 6 (-13032223848971755287))) (.leaf (.eqSym 9 12 8 11955507449361479442))) (.node (.leaf (.eqSym 9 12 9 (-5067824144383367874))) (.leaf (.eqSym 9 13 0 (-241930422168591408)))))
            (.node
            (.node (.leaf (.eqSym 9 13 1 132662911184761611)) (.leaf (.eqSym 9 13 2 2768847851666951348)))
            (.node (.leaf (.eqSym 9 13 3 (-8467538476237732192))) (.node (.leaf (.eqSym 9 13 4 10291870748858439079)) (.leaf (.eqSym 9 13 6 (-16733650043205512630))))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 9 13 7 26723292817474217425)) (.leaf (.eqSym 9 13 8 (-18844540895323576451)))) (.node (.leaf (.eqSym 9 13 9 4870252501529613051)) (.leaf (.eqSym 9 17 0 (-120774398853890121)))))
            (.node (.node (.leaf (.eqSym 9 17 1 1018456660552288599)) (.leaf (.eqSym 9 17 2 (-3264546179137575704)))) (.node (.leaf (.eqSym 9 17 3 4535999818541381261)) (.leaf (.eqSym 9 17 5 (-9682254296924324217))))))
            (.node
            (.node (.node (.leaf (.eqSym 9 17 6 15562171023081766463)) (.leaf (.eqSym 9 17 7 (-12198040449762442550)))) (.node (.leaf (.eqSym 9 17 8 5003427028104334683)) (.leaf (.eqSym 9 17 9 (-859099777272727188)))))
            (.node
            (.node (.leaf (.eqSym 10 11 0 (-4401731866342588990))) (.leaf (.eqSym 10 11 2 (-251223071635051131))))
            (.node (.leaf (.eqSym 10 11 3 9414030692562800952)) (.node (.leaf (.eqSym 10 11 7 3110167325094442790)) (.leaf (.eqSym 10 11 10 (-99318417537829122))))))))))))
      (.node
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 10 12 0 4607429563192712258)) (.leaf (.eqSym 10 12 1 (-1164928138358189826)))) (.node (.leaf (.eqSym 10 12 3 (-6457934160774941721))) (.leaf (.eqSym 10 12 4 (-3880934362649600481)))))
            (.node (.node (.leaf (.eqSym 10 12 6 6179459698597930061)) (.leaf (.eqSym 10 12 7 (-6752593147292109086)))) (.node (.leaf (.eqSym 10 12 8 (-9429062123486937))) (.leaf (.eqSym 10 12 10 187658112079626943)))))
            (.node
            (.node (.node (.leaf (.eqSym 10 13 0 (-1590997472244040003))) (.leaf (.eqSym 10 13 1 762463174651871978))) (.node (.leaf (.eqSym 10 13 3 1910646940224892276)) (.leaf (.eqSym 10 13 4 (-678822568483079081)))))
            (.node (.node (.leaf (.eqSym 10 13 5 5161261796625948284)) (.leaf (.eqSym 10 13 6 (-7475632430465831684)))) (.node (.leaf (.eqSym 10 13 7 4249102663552747464)) (.leaf (.eqSym 10 13 9 29807076403173648))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 10 13 10 (-113253236000433423))) (.leaf (.eqSym 10 17 0 20898435369457733))) (.node (.leaf (.eqSym 10 17 2 (-49027660786577747))) (.leaf (.eqSym 10 17 4 152244555063118806))))
            (.node (.node (.leaf (.eqSym 10 17 5 (-288322933576686547))) (.leaf (.eqSym 10 17 6 167552359078076430))) (.node (.leaf (.eqSym 10 17 9 (-44153148228911061))) (.leaf (.eqSym 10 17 10 16590115201965483)))))
            (.node
            (.node (.node (.leaf (.eqSym 11 12 0 (-2468166529010526482))) (.leaf (.eqSym 11 12 4 23659614779886773435))) (.node (.leaf (.eqSym 11 12 5 (-34857743092051234494))) (.leaf (.eqSym 11 12 6 21118193825178184691))))
            (.node
            (.node (.leaf (.eqSym 11 12 8 (-3786580248317322566))) (.leaf (.eqSym 11 12 9 1251696615005709114)))
            (.node (.leaf (.eqSym 11 12 11 69090725335785161)) (.node (.leaf (.eqSym 11 13 0 1085454590157771844)) (.leaf (.eqSym 11 13 4 (-9345065213173562403)))))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 11 13 5 11657181341138994534)) (.leaf (.eqSym 11 13 6 (-5137519866122650849)))) (.node (.leaf (.eqSym 11 13 8 (-1748567532207107112))) (.leaf (.eqSym 11 13 9 1865790940960018372))))
            (.node (.node (.leaf (.eqSym 11 13 10 (-495182756658492277))) (.leaf (.eqSym 11 13 11 (-73756045537590790)))) (.node (.leaf (.eqSym 11 17 0 (-7718018473460741))) (.leaf (.eqSym 11 17 2 (-250940572689490579))))))
            (.node
            (.node (.node (.leaf (.eqSym 11 17 3 862375716707246987)) (.leaf (.eqSym 11 17 4 (-969803393640196866)))) (.node (.leaf (.eqSym 11 17 6 877204536658973046)) (.leaf (.eqSym 11 17 8 (-1638556109083549843)))))
            (.node
            (.node (.leaf (.eqSym 11 17 9 1916632652056629955)) (.leaf (.eqSym 11 17 10 (-933514505553134108))))
            (.node (.leaf (.eqSym 11 17 11 176839149780678218)) (.node (.leaf (.eqSym 12 13 0 (-466023443032946110))) (.leaf (.eqSym 12 13 1 1290633660691526092)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 12 13 2 (-3511007022661077592))) (.leaf (.eqSym 12 13 3 4020887588144995959))) (.node (.leaf (.eqSym 12 13 7 (-9542060197197731861))) (.leaf (.eqSym 12 13 8 19344502722913148485))))
            (.node (.node (.leaf (.eqSym 12 13 9 (-14923757773075345921))) (.leaf (.eqSym 12 13 10 4612696209801822784))) (.node (.leaf (.eqSym 12 13 12 (-187878396949751567))) (.leaf (.eqSym 12 17 0 (-137393776664494081))))))
            (.node
            (.node (.node (.leaf (.eqSym 12 17 1 711979913341843593)) (.leaf (.eqSym 12 17 3 (-7209310412269066547)))) (.node (.leaf (.eqSym 12 17 4 19988387215977175306)) (.leaf (.eqSym 12 17 5 (-21331771274033040674)))))
            (.node
            (.node (.leaf (.eqSym 12 17 7 21848516652205486246)) (.leaf (.eqSym 12 17 8 (-18097020638961011719))))
            (.node (.leaf (.eqSym 12 17 10 7756425114352992300)) (.node (.leaf (.eqSym 12 17 11 (-4330377553804531237))) (.leaf (.eqSym 12 17 12 784050531724177846)))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 13 17 0 28084052943061558)) (.leaf (.eqSym 13 17 1 (-121101756228542641)))) (.node (.leaf (.eqSym 13 17 3 530148946476409181)) (.leaf (.eqSym 13 17 5 (-2667432719517325310)))))
            (.node (.node (.leaf (.eqSym 13 17 6 3525208760465597380)) (.leaf (.eqSym 13 17 9 (-8760227601609975999)))) (.node (.leaf (.eqSym 13 17 10 15897269138850253514)) (.leaf (.eqSym 13 17 11 (-12511739527624018147))))))
            (.node
            (.node (.node (.leaf (.eqSym 13 17 12 4837880173373349817)) (.leaf (.eqSym 13 17 13 (-755035463580656383)))) (.node (.leaf (.ubPHi 2 769011926284180)) (.leaf (.ubPHi 47 9260797985361))))
            (.node (.node (.leaf (.ubHLePj 5 0 2 691024012755310)) (.leaf (.ubHLePj 5 0 28 17657570048357))) (.node (.leaf (.ubHGe0 5 0 35 17624280936670)) (.leaf (.ubHLePj 5 0 40 12436631943822))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHMcc 5 0 42 4782275845271)) (.leaf (.ubHGe0 5 1 19 37760458685028))) (.node (.leaf (.ubHLePi 5 1 34 6824196644468)) (.leaf (.ubHGe0 5 1 42 1582595617981))))
            (.node (.node (.leaf (.ubHMcc 5 2 0 32559545469799)) (.leaf (.ubHLePj 5 2 26 3606182982855))) (.node (.leaf (.ubHLePj 5 3 25 3755900658487)) (.leaf (.ubHMcc 5 3 38 12753681576517)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 5 3 42 6395734514032)) (.leaf (.ubHLePj 5 4 0 411899764247553))) (.node (.leaf (.ubHGe0 5 4 2 28735828770041)) (.leaf (.ubHGe0 5 4 31 19627118767166))))
            (.node
            (.node (.leaf (.ubHLePj 5 4 37 30744936307823)) (.leaf (.ubHGe0 5 4 41 17368203679866)))
            (.node (.leaf (.ubHLePi 5 4 42 3856880110071)) (.node (.leaf (.ubHLePj 5 5 7 33444509993516)) (.leaf (.ubHGe0 5 5 14 556209300540))))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePj 5 5 22 13872154105980)) (.leaf (.ubHGe0 5 5 30 4509143187687))) (.node (.leaf (.ubHGe0 5 5 41 7944784646659)) (.leaf (.ubHLePj 5 5 42 7147199575621))))
            (.node (.node (.leaf (.ubHGe0 6 0 6 58065579524743)) (.leaf (.ubHLePj 6 0 12 44953773300359))) (.node (.leaf (.ubHGe0 6 0 36 207154809845)) (.leaf (.ubHLePj 6 1 11 76109665074620)))))
            (.node
            (.node (.node (.leaf (.ubHMcc 6 1 27 6611966684499)) (.leaf (.ubHLePj 6 1 39 414648782792))) (.node (.leaf (.ubHMcc 6 2 0 12942636898430)) (.leaf (.ubHLePj 6 2 9 3944865441803))))
            (.node
            (.node (.leaf (.ubHGe0 6 2 18 11123701983648)) (.leaf (.ubHGe0 6 2 41 441591550924)))
            (.node (.leaf (.ubHLePj 6 3 8 71436263784232)) (.node (.leaf (.ubHGe0 6 3 16 6584367382628)) (.leaf (.ubHGe0 6 4 0 221721712243890)))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePj 6 4 24 23108454340255)) (.leaf (.ubHGe0 6 4 32 1800819233446))) (.node (.leaf (.ubHGe0 6 5 14 39552260663297)) (.leaf (.ubHGe0 6 5 30 6632391987456))))
            (.node (.node (.leaf (.ubHLePi 6 5 41 1707276979796)) (.leaf (.ubHGe0 6 6 29 1595302570347))) (.node (.leaf (.ubHLePj 6 6 35 9738706014787)) (.leaf (.ubHGe0 6 6 39 5884136756094)))))
            (.node
            (.node (.node (.leaf (.ubHLePj 6 6 41 621575177490)) (.leaf (.ubHLePj 7 0 28 6635903843905))) (.node (.leaf (.ubHGe0 7 0 36 1602737465681)) (.leaf (.ubHLePj 7 1 1 54872317307793))))
            (.node
            (.node (.leaf (.ubHGe0 7 1 34 753273702974)) (.leaf (.ubHLePj 7 1 40 391728378952)))
            (.node (.leaf (.ubHLePj 7 4 37 5237355480420)) (.node (.leaf (.ubHGe0 7 5 0 56785303285887)) (.leaf (.ubHGe0 7 5 30 4242077663906))))))))))
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 7 5 40 3104878132963)) (.leaf (.ubHGe0 7 6 29 1177097334070))) (.node (.leaf (.ubHGe0 7 7 28 2129702514823)) (.leaf (.ubHGe0 7 7 38 1914751174106))))
            (.node (.node (.leaf (.ubHLePj 7 7 40 2239343466636)) (.leaf (.ubHMcc 8 0 2 365715012070514))) (.node (.leaf (.ubHGe0 8 0 20 4139890506716)) (.leaf (.ubHLePi 8 0 35 1220315673761)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 8 2 33 415249668214)) (.leaf (.ubHLePj 8 2 39 1482711278925))) (.node (.leaf (.ubHMcc 8 3 38 2941434655727)) (.leaf (.ubHLePj 8 5 36 485034207879))))
            (.node (.node (.leaf (.ubHLePj 8 6 22 6079522533007)) (.leaf (.ubHLePi 8 7 39 1323158797548))) (.node (.leaf (.ubHMcc 8 8 39 894925292423)) (.leaf (.ubHMcc 9 0 2 200573370345601))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 9 1 18 673331743316)) (.leaf (.ubHLePj 9 2 0 38994800279916))) (.node (.leaf (.ubHGe0 9 3 32 470234457562)) (.leaf (.ubHMcc 9 4 37 27448626895))))
            (.node (.node (.leaf (.ubHLePj 9 7 21 1869894689474)) (.leaf (.ubHMcc 9 8 4 4542795131598))) (.node (.leaf (.ubHMcc 9 9 3 45314302053665)) (.leaf (.ubHLePi 9 9 10 9737767604236)))))
            (.node
            (.node (.node (.leaf (.ubHMcc 9 9 19 1265533078094)) (.leaf (.ubHLePj 9 9 38 31962775128))) (.node (.leaf (.ubHLePi 10 0 34 1201527103017)) (.leaf (.ubHGe0 10 0 36 1660170334759))))
            (.node
            (.node (.leaf (.ubHGe0 10 1 34 3151115457218)) (.leaf (.ubHLePi 10 2 17 2507697010141)))
            (.node (.leaf (.ubHLePj 10 2 26 5393907965365)) (.node (.leaf (.ubHLePj 10 4 37 1797460974907)) (.leaf (.ubHMcc 10 5 23 8492550570773))))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 10 7 0 32712542732968)) (.leaf (.ubHLePi 10 8 12 4345179475436))) (.node (.leaf (.ubHMcc 10 9 3 9105500973800)) (.leaf (.ubHLePj 10 10 1 100458677448177))))
            (.node (.node (.leaf (.ubHMcc 10 10 17 10353494832964)) (.leaf (.ubHLePi 10 10 25 10118252825235))) (.node (.leaf (.ubHMcc 10 10 31 2813307550043)) (.leaf (.ubHLePi 10 10 36 3959018869738)))))
            (.node
            (.node (.node (.leaf (.ubHMcc 10 10 37 3062932027739)) (.leaf (.ubHGe0 11 0 19 31000652857335))) (.node (.leaf (.ubHMcc 11 0 27 11333522998193)) (.leaf (.ubHLePi 11 0 34 8272439397600))))
            (.node
            (.node (.leaf (.ubHGe0 11 0 36 2026099519708)) (.leaf (.ubHMcc 11 1 1 320546666276942)))
            (.node (.leaf (.ubHLePj 11 2 26 8122370368854)) (.node (.leaf (.ubHGe0 11 4 31 1921119177624)) (.leaf (.ubHLePj 11 5 36 1083049144376)))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHMcc 11 6 22 46382835268760)) (.leaf (.ubHMcc 11 6 34 6945791102463))) (.node (.leaf (.ubHLePi 11 7 28 34418621802704)) (.leaf (.ubHLePi 11 8 36 938097713373))))
            (.node (.node (.leaf (.ubHMcc 11 9 32 14356933303229)) (.leaf (.ubHLePi 11 10 35 4663402287966))) (.node (.leaf (.ubHLePi 11 11 24 1264560616339)) (.leaf (.ubHMcc 11 11 30 12777729681384)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 11 11 34 13062647833419)) (.leaf (.ubHMcc 11 11 36 5797268790462))) (.node (.leaf (.ubHMcc 12 0 30 2870678610756)) (.leaf (.ubHGe0 12 0 35 957955907079))))
            (.node
            (.node (.leaf (.ubHMcc 12 3 9 46457312774989)) (.leaf (.ubHLePi 12 3 35 378275715656)))
            (.node (.leaf (.ubHMcc 12 4 8 23009859684207)) (.node (.leaf (.ubHLePi 12 4 16 15849674502311)) (.leaf (.ubHLePi 12 5 15 64052835397746)))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 12 10 6 12558816051902)) (.leaf (.ubHMcc 12 10 32 3765481148111))) (.node (.leaf (.ubHLePi 12 10 35 2601627582852)) (.leaf (.ubHLePi 12 11 24 6092825179265))))
            (.node (.node (.leaf (.ubHLePi 12 12 4 23091228935758)) (.leaf (.ubHLePi 12 12 33 2616907084969))) (.node (.leaf (.ubHMcc 12 12 35 2345889596776)) (.leaf (.ubHLePi 13 0 20 24161383808566)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 13 0 21 10806529868301)) (.leaf (.ubHMcc 13 0 30 667273984671))) (.node (.leaf (.ubHLePj 13 1 26 3343919386761)) (.leaf (.ubHLePi 13 1 34 1217179138000))))
            (.node
            (.node (.leaf (.ubHMcc 13 2 0 33579691471165)) (.leaf (.ubHMcc 13 3 25 3278507286420)))
            (.node (.leaf (.ubHGe0 13 3 32 4411910479458)) (.node (.leaf (.ubHMcc 13 4 24 7968896551431)) (.leaf (.ubHLePi 13 5 31 6399464945177)))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 13 5 32 1324287368715)) (.leaf (.ubHGe0 13 7 28 422715307040))) (.node (.leaf (.ubHMcc 13 8 34 3077645528770)) (.leaf (.ubHMcc 13 11 0 48358359958211))))
            (.node (.node (.leaf (.ubHMcc 13 11 17 5724263500150)) (.leaf (.ubHLePi 13 11 24 621894683133))) (.node (.leaf (.ubHMcc 13 11 30 2365498770557)) (.leaf (.ubHLePi 13 11 34 5836342601325)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 13 12 7 6671276016400)) (.leaf (.ubHLePi 13 12 24 4091820795405))) (.node (.leaf (.ubHGe0 13 12 34 5246886402089)) (.leaf (.ubHGe0 13 13 6 6945861620724))))
            (.node
            (.node (.leaf (.ubHLePj 13 13 14 5218283274252)) (.leaf (.ubHGe0 13 13 22 4576122432893)))
            (.node (.leaf (.ubHLePj 13 13 28 893247300282)) (.node (.leaf (.ubHGe0 13 13 33 469651710914)) (.leaf (.ubHLePj 13 13 34 1794784034024))))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 17 0 19 5810741659694)) (.leaf (.ubHLePj 17 0 27 1802418256309))) (.node (.leaf (.ubHMcc 17 0 28 1021977431712)) (.leaf (.ubHLePj 17 1 1 127017159476442))))
            (.node (.node (.leaf (.ubHGe0 17 1 18 5964946889392)) (.leaf (.ubHMcc 17 1 27 459358341758))) (.node (.leaf (.ubHLePj 17 2 0 4012202196418)) (.leaf (.ubHLePj 17 3 24 2661830250066)))))
            (.node
            (.node (.node (.leaf (.ubHLePj 17 4 23 972794090143)) (.leaf (.ubHGe0 17 5 29 2221157178208))) (.node (.leaf (.ubHLePi 17 5 30 948413834671)) (.leaf (.ubHGe0 17 6 13 12529491193062))))
            (.node
            (.node (.leaf (.ubHGe0 17 6 28 886642430314)) (.leaf (.ubHLePi 17 6 30 840848376188)))
            (.node (.leaf (.ubHGe0 17 7 12 5443294847145)) (.node (.leaf (.ubHGe0 17 9 10 1730168087104)) (.leaf (.ubHLePj 17 9 19 9235982874747)))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 17 10 9 679741841305)) (.leaf (.ubHGe0 17 11 24 3898436636742))) (.node (.leaf (.ubHLePj 17 12 0 932869009552)) (.leaf (.ubHLePj 17 12 16 1166051362358))))
            (.node (.node (.leaf (.ubHGe0 17 12 23 4628119156895)) (.leaf (.ubHLePj 17 13 15 1520615952989))) (.node (.leaf (.ubHLePj 17 13 28 3721941741558)) (.leaf (.ubHGe0 17 14 5 1060102557882)))))
            (.node
            (.node (.node (.leaf (.ubHLePj 17 14 27 2723385860436)) (.leaf (.ubHGe0 17 15 30 5028334357203))) (.node (.leaf (.ubHLePi 17 16 4 1173023280440)) (.leaf (.ubHLePj 17 16 11 720684501966))))
            (.node
            (.node (.leaf (.ubHGe0 17 16 19 1900415795694)) (.leaf (.ubHLePi 17 16 30 3361310933768)))
            (.node (.leaf (.ubHLePi 17 17 2 1052795164475)) (.node (.leaf (.ubHGe0 17 17 3 1542690077798)) (.leaf (.ubHGe0 17 17 18 451720930717))))))))))))
    (.node
      (.node
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePj 17 17 24 2842681027431)) (.leaf (.ubHGe0 17 17 28 3705204443680))) (.node (.leaf (.ubHLePj 17 17 30 1078252279223)) (.leaf (.ubHLePi 5 0 9 30115405))))
            (.node (.node (.leaf (.ubHGe0 5 1 8 152893179)) (.leaf (.ubHGe0 5 2 7 89068414))) (.node (.leaf (.ubHGe0 5 3 6 18750694)) (.leaf (.ubHGe0 5 4 5 1761597)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 5 5 4 55915)) (.leaf (.ubHGe0 5 0 8 103834363))) (.node (.leaf (.ubHLePi 5 1 7 1367875917)) (.leaf (.ubHLePi 5 2 6 662126524))))
            (.node (.node (.leaf (.ubHLePi 5 3 5 116324300)) (.leaf (.ubHLePi 5 4 4 8832790))) (.node (.leaf (.ubHLePi 5 5 3 217204)) (.leaf (.ubHGe0 5 0 7 304421888))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 5 1 6 5321534092)) (.leaf (.ubHGe0 5 2 5 2106202882))) (.node (.leaf (.ubHGe0 5 3 4 300366592)) (.leaf (.ubHGe0 5 4 3 17712461))))
            (.node (.node (.leaf (.ubHGe0 5 5 2 316670)) (.leaf (.ubHLePi 5 0 6 2517308509))) (.node (.leaf (.ubHLePi 5 1 5 11768109715)) (.leaf (.ubHLePi 5 2 4 3716507489)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 5 3 3 413236481)) (.leaf (.ubHLePi 5 4 2 17756817))) (.node (.leaf (.ubHLePi 5 5 1 205361)) (.leaf (.ubHGe0 5 0 5 6691048189))))
            (.node
            (.node (.leaf (.ubHGe0 5 1 4 16190624519)) (.leaf (.ubHGe0 5 2 3 3929137532)))
            (.node (.leaf (.ubHGe0 5 3 2 319492581)) (.node (.leaf (.ubHGe0 5 4 1 8899418)) (.leaf (.ubHGe0 5 5 0 49980))))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 5 0 4 9824266270)) (.leaf (.ubHLePi 5 1 3 14198448478))) (.node (.leaf (.ubHLePi 5 2 2 2488935327)) (.leaf (.ubHLePi 5 3 1 131624743))))
            (.node (.node (.leaf (.ubHLePi 5 4 0 1783869)) (.leaf (.ubHGe0 5 0 3 8792954260))) (.node (.leaf (.ubHGe0 5 1 2 7754069019)) (.leaf (.ubHGe0 5 2 1 874753838)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 5 3 0 22575657)) (.leaf (.ubHLePi 5 0 2 4800186905))) (.node (.leaf (.ubHLePi 5 1 1 2411960679)) (.leaf (.ubHLePi 5 2 0 131593327))))
            (.node
            (.node (.leaf (.ubHGe0 5 0 1 1476596725)) (.leaf (.ubHGe0 5 1 0 327273980)))
            (.node (.leaf (.ubHLePi 5 0 0 196978337)) (.node (.leaf (.ubHGe0 6 0 9 432020550)) (.leaf (.ubHGe0 6 1 8 507448168)))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 6 2 7 248224019)) (.leaf (.ubHGe0 6 3 6 60980791))) (.node (.leaf (.ubHGe0 6 4 5 7313271)) (.leaf (.ubHGe0 6 5 4 377821))))
            (.node (.node (.leaf (.ubHGe0 6 6 3 6288)) (.leaf (.ubHLePi 6 0 8 4274744536))) (.node (.leaf (.ubHLePi 6 1 7 4432537858)) (.leaf (.ubHLePi 6 2 6 1868706645)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 6 3 5 384475410)) (.leaf (.ubHLePi 6 4 4 37416244))) (.node (.leaf (.ubHLePi 6 5 3 1507210)) (.leaf (.ubHLePi 6 6 2 18361))))
            (.node
            (.node (.leaf (.ubHGe0 6 0 7 18799285798)) (.leaf (.ubHGe0 6 1 6 16924244892)))
            (.node (.leaf (.ubHGe0 6 2 5 6020488939)) (.node (.leaf (.ubHGe0 6 3 4 1008805736)) (.leaf (.ubHGe0 6 4 3 76532962)))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 6 5 2 2255050)) (.leaf (.ubHGe0 6 6 1 17882))) (.node (.leaf (.ubHLePi 6 0 6 48220656444)) (.leaf (.ubHLePi 6 1 5 36890174819))))
            (.node (.node (.leaf (.ubHLePi 6 2 4 10760493306)) (.leaf (.ubHLePi 6 3 3 1410084597))) (.node (.leaf (.ubHLePi 6 4 2 78234068)) (.leaf (.ubHLePi 6 5 1 1499734)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 6 6 0 5809)) (.leaf (.ubHGe0 6 0 5 79492333008))) (.node (.leaf (.ubHGe0 6 1 4 50204997999)) (.leaf (.ubHGe0 6 2 3 11523381196))))
            (.node (.node (.leaf (.ubHGe0 6 3 2 1107461619)) (.leaf (.ubHGe0 6 4 1 39967875))) (.node (.leaf (.ubHGe0 6 5 0 374074)) (.leaf (.ubHLePi 6 0 4 87329345286))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 6 1 3 43681413509)) (.leaf (.ubHLePi 6 2 2 7394177458))) (.node (.leaf (.ubHLePi 6 3 1 463400087)) (.leaf (.ubHLePi 6 4 0 8163795))))
            (.node (.node (.leaf (.ubHGe0 6 0 3 63928145452)) (.leaf (.ubHGe0 6 1 2 23727073753))) (.node (.leaf (.ubHGe0 6 2 1 2632411613)) (.leaf (.ubHGe0 6 3 0 80711948)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 6 0 2 30066742550)) (.leaf (.ubHLePi 6 1 1 7356314557))) (.node (.leaf (.ubHLePi 6 2 0 401128358)) (.leaf (.ubHGe0 6 0 1 8243474268))))
            (.node
            (.node (.leaf (.ubHGe0 6 1 0 996675932)) (.leaf (.ubHLePi 6 0 0 1003770260)))
            (.node (.leaf (.ubHGe0 7 0 9 283646616)) (.node (.leaf (.ubHGe0 7 1 8 416222401)) (.leaf (.ubHGe0 7 2 7 296957774))))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 7 3 6 104215826)) (.leaf (.ubHGe0 7 4 5 18458360))) (.node (.leaf (.ubHGe0 7 5 4 1606294)) (.leaf (.ubHGe0 7 6 3 61255))))
            (.node (.node (.leaf (.ubHGe0 7 7 2 747)) (.leaf (.ubHLePi 7 0 8 2883599015))) (.node (.leaf (.ubHLePi 7 1 7 3816374362)) (.leaf (.ubHLePi 7 2 6 2326271313)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 7 3 5 680062980)) (.leaf (.ubHLePi 7 4 4 97576538))) (.node (.leaf (.ubHLePi 7 5 3 6605318)) (.leaf (.ubHLePi 7 6 2 183688))))
            (.node
            (.node (.leaf (.ubHLePi 7 7 1 1450)) (.leaf (.ubHGe0 7 0 7 13069450901)))
            (.node (.leaf (.ubHGe0 7 1 6 15266600201)) (.node (.leaf (.ubHGe0 7 2 5 7787068580)) (.leaf (.ubHGe0 7 3 4 1845011907)))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 7 4 3 206026976)) (.leaf (.ubHGe0 7 5 2 10178354))) (.node (.leaf (.ubHGe0 7 6 1 183617)) (.leaf (.ubHGe0 7 7 0 704))))
            (.node (.node (.leaf (.ubHLePi 7 0 6 34629584610)) (.leaf (.ubHLePi 7 1 5 34800417248))) (.node (.leaf (.ubHLePi 7 2 4 14441138181)) (.leaf (.ubHLePi 7 3 3 2664037386)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 7 4 2 217205156)) (.leaf (.ubHLePi 7 5 1 6965922))) (.node (.leaf (.ubHLePi 7 6 0 61184)) (.leaf (.ubHGe0 7 0 5 59069017183))))
            (.node
            (.node (.leaf (.ubHGe0 7 1 4 49443281846)) (.leaf (.ubHGe0 7 2 3 16025953029)))
            (.node (.leaf (.ubHGe0 7 3 2 2159433101)) (.node (.leaf (.ubHGe0 7 4 1 114343747)) (.leaf (.ubHLePi 7 0 4 67220076604))))))))))
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 7 1 3 44836368712)) (.leaf (.ubHLePi 7 2 2 10643759314))) (.node (.leaf (.ubHLePi 7 3 1 931781731)) (.leaf (.ubHLePi 7 4 0 24047389))))
            (.node (.node (.leaf (.ubHGe0 7 0 3 51006284771)) (.leaf (.ubHGe0 7 1 2 25344219113))) (.node (.leaf (.ubHGe0 7 2 1 3917792834)) (.leaf (.ubHGe0 7 3 0 167221263)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 7 0 2 24873771932)) (.leaf (.ubHLePi 7 1 1 8165133104))) (.node (.leaf (.ubHLePi 7 2 0 616603408)) (.leaf (.ubHGe0 7 0 1 7071233982))))
            (.node (.node (.leaf (.ubHGe0 7 1 0 1147969865)) (.leaf (.ubHLePi 7 0 0 892601293))) (.node (.leaf (.ubHGe0 8 0 9 175436984)) (.leaf (.ubHGe0 8 1 8 47587895))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 8 2 7 55170429)) (.leaf (.ubHLePi 8 3 6 38708463))) (.node (.leaf (.ubHLePi 8 4 5 10524024)) (.leaf (.ubHLePi 8 5 4 1442702))))
            (.node (.node (.leaf (.ubHLePi 8 6 3 96368)) (.leaf (.ubHLePi 8 7 2 2770))) (.node (.leaf (.ubHLePi 8 8 1 27)) (.leaf (.ubHLePi 8 0 8 1573862788)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 8 1 7 258562668)) (.leaf (.ubHGe0 8 2 6 490470541))) (.node (.leaf (.ubHGe0 8 3 5 267528444)) (.leaf (.ubHGe0 8 4 4 58340678))))
            (.node
            (.node (.leaf (.ubHGe0 8 5 3 6188052)) (.leaf (.ubHGe0 8 6 2 300137)))
            (.node (.leaf (.ubHGe0 8 7 1 5556)) (.node (.leaf (.ubHGe0 8 8 0 25)) (.leaf (.ubHGe0 8 0 7 6221865661))))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 8 1 6 387571575)) (.leaf (.ubHLePi 8 2 5 1829018507))) (.node (.leaf (.ubHLePi 8 3 4 766433705)) (.leaf (.ubHLePi 8 4 3 128928686))))
            (.node (.node (.leaf (.ubHLePi 8 5 2 9930052)) (.leaf (.ubHLePi 8 6 1 311165))) (.node (.leaf (.ubHLePi 8 7 0 2786)) (.leaf (.ubHLePi 8 0 6 14194247447)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 8 1 5 465737294)) (.leaf (.ubHGe0 8 2 4 3727067730))) (.node (.leaf (.ubHGe0 8 3 3 1165493541)) (.leaf (.ubHGe0 8 4 2 142009613))))
            (.node
            (.node (.leaf (.ubHGe0 8 5 1 7066747)) (.leaf (.ubHGe0 8 6 0 107397)))
            (.node (.leaf (.ubHGe0 8 0 5 20531869499)) (.node (.leaf (.ubHLePi 8 1 4 2427199143)) (.leaf (.ubHLePi 8 2 3 4497074342)))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 8 3 2 992557532)) (.leaf (.ubHLePi 8 4 1 77975765))) (.node (.leaf (.ubHLePi 8 5 0 1882045)) (.leaf (.ubHLePi 8 0 4 19444962520))))
            (.node (.node (.leaf (.ubHGe0 8 1 3 3684952088)) (.leaf (.ubHGe0 8 2 2 3220533992))) (.node (.leaf (.ubHGe0 8 3 1 448977832)) (.leaf (.ubHGe0 8 4 0 17078183)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 8 0 3 11980390540)) (.leaf (.ubHLePi 8 1 2 2865256173))) (.node (.leaf (.ubHLePi 8 2 1 1269653567)) (.leaf (.ubHLePi 8 3 0 84300117))))
            (.node
            (.node (.leaf (.ubHLePi 8 0 2 4583131371)) (.leaf (.ubHGe0 8 1 1 1159572240)))
            (.node (.leaf (.ubHGe0 8 2 0 212844582)) (.node (.leaf (.ubHGe0 8 0 1 969988229)) (.leaf (.ubHLePi 8 1 0 194403109)))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 8 0 0 83346785)) (.leaf (.ubHGe0 9 0 9 43590822))) (.node (.leaf (.ubHGe0 9 1 8 87899238)) (.leaf (.ubHGe0 9 2 7 74734082))))
            (.node (.node (.leaf (.ubHGe0 9 3 6 34548928)) (.leaf (.ubHGe0 9 4 5 9119855))) (.node (.leaf (.ubHGe0 9 5 4 1351974)) (.leaf (.ubHGe0 9 6 3 108957)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 9 7 2 4625)) (.leaf (.ubHGe0 9 8 1 95))) (.node (.leaf (.ubHGe0 9 9 0 1)) (.leaf (.ubHLePi 9 0 8 466851728))))
            (.node
            (.node (.leaf (.ubHLePi 9 1 7 829720793)) (.leaf (.ubHLePi 9 2 6 610388645)))
            (.node (.leaf (.ubHLePi 9 3 5 237491238)) (.node (.leaf (.ubHLePi 9 4 4 51006638)) (.leaf (.ubHLePi 9 5 3 5899557)))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 9 6 2 348523)) (.leaf (.ubHLePi 9 7 1 9637))) (.node (.leaf (.ubHLePi 9 8 0 96)) (.leaf (.ubHGe0 9 0 7 2220861483))))
            (.node (.node (.leaf (.ubHGe0 9 1 6 3422791808)) (.leaf (.ubHGe0 9 2 5 2131779117))) (.node (.leaf (.ubHGe0 9 3 4 678261588)) (.leaf (.ubHGe0 9 4 3 113813510)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 9 5 2 9635530)) (.leaf (.ubHGe0 9 6 1 371074))) (.node (.leaf (.ubHGe0 9 7 0 5012)) (.leaf (.ubHLePi 9 0 6 6158247212))))
            (.node
            (.node (.leaf (.ubHLePi 9 1 5 8057651887)) (.leaf (.ubHLePi 9 2 4 4126508911)))
            (.node (.leaf (.ubHLePi 9 3 3 1030206351)) (.node (.leaf (.ubHLePi 9 4 2 126664042)) (.leaf (.ubHLePi 9 5 1 6981635))))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 9 6 0 131509)) (.leaf (.ubHGe0 9 0 5 10967687153))) (.node (.leaf (.ubHGe0 9 1 4 11837055009)) (.leaf (.ubHGe0 9 2 3 4781028203))))
            (.node (.node (.leaf (.ubHGe0 9 3 2 877782113)) (.leaf (.ubHGe0 9 4 1 70316195))) (.node (.leaf (.ubHGe0 9 5 0 1893689)) (.leaf (.ubHLePi 9 0 4 13008305001)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 9 1 3 11109913234)) (.leaf (.ubHLePi 9 2 2 3315436127))) (.node (.leaf (.ubHLePi 9 3 1 397829798)) (.leaf (.ubHLePi 9 4 0 15578879))))
            (.node
            (.node (.leaf (.ubHGe0 9 0 3 10273245125)) (.leaf (.ubHGe0 9 1 2 6505017517)))
            (.node (.leaf (.ubHGe0 9 2 1 1274121396)) (.node (.leaf (.ubHGe0 9 3 0 74934759)) (.leaf (.ubHLePi 9 0 2 5208582066)))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 9 1 1 2172155221)) (.leaf (.ubHLePi 9 2 0 209329114))) (.node (.leaf (.ubHGe0 9 0 1 1538162332)) (.leaf (.ubHGe0 9 1 0 316677564))))
            (.node (.node (.leaf (.ubHLePi 9 0 0 201560907)) (.leaf (.ubHGe0 10 0 9 124313099))) (.node (.leaf (.ubHGe0 10 1 8 195643123)) (.leaf (.ubHGe0 10 2 7 173793551)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 10 3 6 90163922)) (.leaf (.ubHGe0 10 4 5 27520514))) (.node (.leaf (.ubHGe0 10 5 4 4747649)) (.leaf (.ubHGe0 10 6 3 442760))))
            (.node
            (.node (.leaf (.ubHGe0 10 7 2 21232)) (.leaf (.ubHGe0 10 8 1 459)))
            (.node (.leaf (.ubHGe0 10 9 0 1)) (.node (.leaf (.ubHLePi 10 0 8 1274713685)) (.leaf (.ubHLePi 10 1 7 1860506265)))))))))))
      (.node
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 10 2 6 1448224965)) (.leaf (.ubHLePi 10 3 5 634624202))) (.node (.leaf (.ubHLePi 10 4 4 157357915)) (.leaf (.ubHLePi 10 5 3 21118511))))
            (.node (.node (.leaf (.ubHLePi 10 6 2 1440351)) (.leaf (.ubHLePi 10 7 1 44974))) (.node (.leaf (.ubHLePi 10 8 0 466)) (.leaf (.ubHGe0 10 0 7 5854899225)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 10 1 6 7750091028)) (.leaf (.ubHGe0 10 2 5 5162587066))) (.node (.leaf (.ubHGe0 10 3 4 1854588511)) (.leaf (.ubHGe0 10 4 3 358666174))))
            (.node (.node (.leaf (.ubHGe0 10 5 2 35139114)) (.leaf (.ubHGe0 10 6 1 1559026))) (.node (.leaf (.ubHGe0 10 7 0 23758)) (.leaf (.ubHLePi 10 0 6 15795141973))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 10 1 5 18458738580)) (.leaf (.ubHLePi 10 2 4 10202025476))) (.node (.leaf (.ubHLePi 10 3 3 2880462063)) (.leaf (.ubHLePi 10 4 2 407430536))))
            (.node (.node (.leaf (.ubHLePi 10 5 1 25923878)) (.leaf (.ubHLePi 10 6 0 561463))) (.node (.leaf (.ubHGe0 10 0 5 27554991374)) (.leaf (.ubHGe0 10 1 4 27478228463)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 10 2 3 12067285003)) (.leaf (.ubHGe0 10 3 2 2507959682))) (.node (.leaf (.ubHGe0 10 4 1 230702690)) (.leaf (.ubHGe0 10 5 0 7155660))))
            (.node
            (.node (.leaf (.ubHLePi 10 0 4 32205148420)) (.leaf (.ubHLePi 10 1 3 26166827643)))
            (.node (.leaf (.ubHLePi 10 2 2 8542031767)) (.node (.leaf (.ubHLePi 10 3 1 1160757307)) (.leaf (.ubHLePi 10 4 0 52100955))))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 10 0 3 25193892626)) (.leaf (.ubHGe0 10 1 2 15559806710))) (.node (.leaf (.ubHGe0 10 2 1 3350173338)) (.leaf (.ubHGe0 10 3 0 223131474))))
            (.node (.node (.leaf (.ubHLePi 10 0 2 12709749847)) (.leaf (.ubHLePi 10 1 1 5280499584))) (.node (.leaf (.ubHLePi 10 2 0 561556756)) (.leaf (.ubHGe0 10 0 1 3748907579)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 10 1 0 782802749)) (.leaf (.ubHLePi 10 0 0 492249978))) (.node (.leaf (.ubHLePi 11 0 9 87405681)) (.leaf (.ubHLePi 11 1 8 276659673))))
            (.node
            (.node (.leaf (.ubHLePi 11 2 7 382529908)) (.leaf (.ubHLePi 11 3 6 265606336)))
            (.node (.leaf (.ubHLePi 11 4 5 102396717)) (.node (.leaf (.ubHLePi 11 5 4 22519834)) (.leaf (.ubHLePi 11 6 3 2765723)))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 11 7 2 176890)) (.leaf (.ubHLePi 11 8 1 5249))) (.node (.leaf (.ubHLePi 11 9 0 98)) (.leaf (.ubHGe0 11 0 8 1033772767))))
            (.node (.node (.leaf (.ubHGe0 11 1 7 2897395231)) (.leaf (.ubHGe0 11 2 6 3380032672))) (.node (.leaf (.ubHGe0 11 3 5 1948902212)) (.leaf (.ubHGe0 11 4 4 607747029)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 11 5 3 103825600)) (.leaf (.ubHGe0 11 6 2 9284436))) (.node (.leaf (.ubHGe0 11 7 1 385301)) (.leaf (.ubHGe0 11 8 0 5838))))
            (.node
            (.node (.leaf (.ubHLePi 11 0 7 5433775920)) (.leaf (.ubHLePi 11 1 6 13163153340)))
            (.node (.leaf (.ubHLePi 11 2 5 12717810942)) (.node (.leaf (.ubHLePi 11 3 4 5927206712)) (.leaf (.ubHLePi 11 4 3 1436398852)))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 11 5 2 178825822)) (.leaf (.ubHLePi 11 6 1 10360261))) (.node (.leaf (.ubHLePi 11 7 0 210185)) (.leaf (.ubHGe0 11 0 6 16621879903))))
            (.node (.node (.leaf (.ubHGe0 11 1 5 33907739914)) (.leaf (.ubHGe0 11 2 4 26424922859))) (.node (.leaf (.ubHGe0 11 3 3 9566162839)) (.leaf (.ubHGe0 11 4 2 1690209398)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 11 5 1 136402133)) (.leaf (.ubHGe0 11 6 0 3844869))) (.node (.leaf (.ubHLePi 11 0 5 32563885815)) (.leaf (.ubHLePi 11 1 4 54200435550))))
            (.node
            (.node (.leaf (.ubHLePi 11 2 3 32756494380)) (.leaf (.ubHLePi 11 3 2 8643263922)))
            (.node (.leaf (.ubHLePi 11 4 1 990385546)) (.node (.leaf (.ubHLePi 11 5 0 38886235)) (.leaf (.ubHGe0 11 0 4 42334452524)))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 11 1 3 55079724994)) (.leaf (.ubHGe0 11 2 2 24232341413))) (.node (.leaf (.ubHGe0 11 3 1 4146104417)) (.leaf (.ubHGe0 11 4 0 231228256))))
            (.node (.node (.leaf (.ubHLePi 11 0 3 36504834852)) (.leaf (.ubHLePi 11 1 2 34765984402))) (.node (.leaf (.ubHLePi 11 2 1 9908372610)) (.leaf (.ubHLePi 11 3 0 825094581)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 11 0 2 20128774524)) (.leaf (.ubHGe0 11 1 1 12466279996))) (.node (.leaf (.ubHGe0 11 2 0 1727911689)) (.leaf (.ubHLePi 11 0 1 6439805955))))
            (.node
            (.node (.leaf (.ubHLePi 11 1 0 1944907349)) (.leaf (.ubHGe0 11 0 0 910828523)))
            (.node (.leaf (.ubHLePi 12 0 9 6375508)) (.node (.leaf (.ubHGe0 12 1 8 392478)) (.leaf (.ubHLePi 12 2 7 43988211))))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 12 3 6 65667880)) (.leaf (.ubHLePi 12 4 5 41941736))) (.node (.leaf (.ubHLePi 12 5 4 13804180)) (.leaf (.ubHLePi 12 6 3 2419917))))
            (.node (.node (.leaf (.ubHLePi 12 7 2 218209)) (.leaf (.ubHLePi 12 8 1 8974))) (.node (.leaf (.ubHLePi 12 9 0 76)) (.leaf (.ubHGe0 12 0 8 54171848)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 12 1 7 81287583)) (.leaf (.ubHGe0 12 2 6 489220160))) (.node (.leaf (.ubHGe0 12 3 5 545048929)) (.leaf (.ubHGe0 12 4 4 270563763))))
            (.node
            (.node (.leaf (.ubHGe0 12 5 3 67705152)) (.leaf (.ubHGe0 12 6 2 8530956)))
            (.node (.leaf (.ubHGe0 12 7 1 493286)) (.node (.leaf (.ubHGe0 12 8 0 9475)) (.leaf (.ubHLePi 12 0 7 245311609)))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 12 1 6 747463230)) (.leaf (.ubHLePi 12 2 5 2217357300))) (.node (.leaf (.ubHLePi 12 3 4 1848985272)) (.leaf (.ubHLePi 12 4 3 690213536))))
            (.node (.node (.leaf (.ubHLePi 12 5 2 123555142)) (.leaf (.ubHLePi 12 6 1 9966992))) (.node (.leaf (.ubHLePi 12 7 0 276657)) (.leaf (.ubHGe0 12 0 6 787437773)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 12 1 5 2881377169)) (.leaf (.ubHGe0 12 2 4 5386339559))) (.node (.leaf (.ubHGe0 12 3 3 3291300451)) (.leaf (.ubHGe0 12 4 2 871431585))))
            (.node
            (.node (.leaf (.ubHGe0 12 5 1 99492919)) (.leaf (.ubHGe0 12 6 0 3859003)))
            (.node (.leaf (.ubHLePi 12 0 5 1832391160)) (.node (.leaf (.ubHLePi 12 1 4 6112277073)) (.leaf (.ubHLePi 12 2 3 7638553861))))))))))
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 12 3 2 3249684877)) (.leaf (.ubHLePi 12 4 1 545075737))) (.node (.leaf (.ubHLePi 12 5 0 29842653)) (.leaf (.ubHGe0 12 0 4 2955807281))))
            (.node (.node (.leaf (.ubHGe0 12 1 3 7725545671)) (.leaf (.ubHGe0 12 2 2 6358926615))) (.node (.leaf (.ubHGe0 12 3 1 1690389792)) (.leaf (.ubHGe0 12 4 0 135239066)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 12 0 3 3161468959)) (.leaf (.ubHLePi 12 1 2 5823516735))) (.node (.leaf (.ubHLePi 12 2 1 2888264646)) (.leaf (.ubHLePi 12 3 0 362403155))))
            (.node (.node (.leaf (.ubHGe0 12 0 2 2126248921)) (.leaf (.ubHGe0 12 1 1 2425270743))) (.node (.leaf (.ubHGe0 12 2 0 553678458)) (.leaf (.ubHLePi 12 0 1 812807767))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 12 1 0 430616781)) (.leaf (.ubHGe0 12 0 0 134689199))) (.node (.leaf (.ubHGe0 13 0 9 6486870)) (.leaf (.ubHGe0 13 1 8 105753838))))
            (.node (.node (.leaf (.ubHGe0 13 2 7 170765494)) (.leaf (.ubHGe0 13 3 6 121329789))) (.node (.leaf (.ubHGe0 13 4 5 42303152)) (.leaf (.ubHGe0 13 5 4 5871328)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 13 6 3 285278)) (.leaf (.ubHLePi 13 7 2 159029))) (.node (.leaf (.ubHLePi 13 8 1 14430)) (.leaf (.ubHLePi 13 9 0 544))))
            (.node
            (.node (.leaf (.ubHLePi 13 0 8 162306153)) (.leaf (.ubHLePi 13 1 7 1158560743)))
            (.node (.leaf (.ubHLePi 13 2 6 1521537649)) (.node (.leaf (.ubHLePi 13 3 5 876890246)) (.leaf (.ubHLePi 13 4 4 236302264))))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 13 5 3 21706824)) (.leaf (.ubHGe0 13 6 2 1840831))) (.node (.leaf (.ubHGe0 13 7 1 415630)) (.leaf (.ubHGe0 13 8 0 18353))))
            (.node (.node (.leaf (.ubHGe0 13 0 7 1207088778)) (.leaf (.ubHGe0 13 1 6 5443749761))) (.node (.leaf (.ubHGe0 13 2 5 5742661776)) (.leaf (.ubHGe0 13 3 4 2607347040)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 13 4 3 517771660)) (.leaf (.ubHGe0 13 5 2 27252071))) (.node (.leaf (.ubHLePi 13 6 1 3120888)) (.leaf (.ubHLePi 13 7 0 269634))))
            (.node
            (.node (.leaf (.ubHLePi 13 0 6 4539968219)) (.leaf (.ubHLePi 13 1 5 14375246159)))
            (.node (.leaf (.ubHLePi 13 2 4 11904703842)) (.node (.leaf (.ubHLePi 13 3 3 4081374497)) (.leaf (.ubHLePi 13 4 2 554561953)))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 13 5 1 12349954)) (.leaf (.ubHGe0 13 6 0 1591322))) (.node (.leaf (.ubHGe0 13 0 5 10190152435)) (.leaf (.ubHGe0 13 1 4 23383605909))))
            (.node (.node (.leaf (.ubHGe0 13 2 3 14642041210)) (.leaf (.ubHGe0 13 3 2 3545383020))) (.node (.leaf (.ubHGe0 13 4 1 288923505)) (.leaf (.ubHGe0 13 5 0 899363)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 13 0 4 14558286430)) (.leaf (.ubHLePi 13 1 3 24027972436))) (.node (.leaf (.ubHLePi 13 2 2 10685540718)) (.leaf (.ubHLePi 13 3 1 1619140460))))
            (.node
            (.node (.leaf (.ubHLePi 13 4 0 58103928)) (.leaf (.ubHGe0 13 0 3 13426874713)))
            (.node (.leaf (.ubHGe0 13 1 2 15246553218)) (.node (.leaf (.ubHGe0 13 2 1 4284141474)) (.leaf (.ubHGe0 13 3 0 303327282)))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 13 0 2 7770644964)) (.leaf (.ubHLePi 13 1 1 5465936142))) (.node (.leaf (.ubHLePi 13 2 0 727820714)) (.leaf (.ubHGe0 13 0 1 2573298818))))
            (.node (.node (.leaf (.ubHGe0 13 1 0 848051145)) (.leaf (.ubHLePi 13 0 0 372695684))) (.node (.leaf (.ubHLePi 17 0 9 899016)) (.leaf (.ubHLePi 17 1 8 21493232)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 17 2 7 58480770)) (.leaf (.ubHLePi 17 3 6 85911386))) (.node (.leaf (.ubHLePi 17 4 5 75615338)) (.leaf (.ubHLePi 17 5 4 41426834))))
            (.node
            (.node (.leaf (.ubHLePi 17 6 3 14184723)) (.leaf (.ubHLePi 17 7 2 2956441)))
            (.node (.leaf (.ubHLePi 17 8 1 358859)) (.node (.leaf (.ubHLePi 17 9 0 21041)) (.leaf (.ubHGe0 17 0 8 29691378)))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 17 1 7 282430571)) (.leaf (.ubHGe0 17 2 6 650968337))) (.node (.leaf (.ubHGe0 17 3 5 797183237)) (.leaf (.ubHGe0 17 4 4 569620978))))
            (.node (.node (.leaf (.ubHGe0 17 5 3 243755790)) (.leaf (.ubHGe0 17 6 2 61343863))) (.node (.leaf (.ubHGe0 17 7 1 8487308)) (.leaf (.ubHGe0 17 8 0 525915)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 17 0 7 256965278)) (.leaf (.ubHLePi 17 1 6 1602308014))) (.node (.leaf (.ubHLePi 17 2 5 3072940989)) (.leaf (.ubHLePi 17 3 4 3053361718))))
            (.node
            (.node (.leaf (.ubHLePi 17 4 3 1702431599)) (.leaf (.ubHLePi 17 5 2 534302186)))
            (.node (.leaf (.ubHLePi 17 6 1 88297650)) (.node (.leaf (.ubHLePi 17 7 0 6128480)) (.leaf (.ubHGe0 17 0 6 1114437999))))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 17 1 5 5133855639)) (.leaf (.ubHGe0 17 2 4 7979617073))) (.node (.leaf (.ubHGe0 17 3 3 6182757339)) (.leaf (.ubHGe0 17 4 2 2524982632))))
            (.node (.node (.leaf (.ubHGe0 17 5 1 517967245)) (.leaf (.ubHGe0 17 6 0 42399484))) (.node (.leaf (.ubHLePi 17 0 5 2898061095)) (.leaf (.ubHLePi 17 1 4 10171175576)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 17 2 3 12317570497)) (.leaf (.ubHLePi 17 3 2 6984756722))) (.node (.leaf (.ubHLePi 17 4 1 1860250864)) (.leaf (.ubHLePi 17 5 0 187720122))))
            (.node
            (.node (.leaf (.ubHGe0 17 0 4 4831771896)) (.leaf (.ubHGe0 17 1 3 12769318275)))
            (.node (.leaf (.ubHGe0 17 2 2 11309090950)) (.node (.leaf (.ubHGe0 17 3 1 4176967706)) (.leaf (.ubHGe0 17 4 0 545281456)))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 17 0 3 5237816521)) (.leaf (.ubHLePi 17 1 2 9926896864))) (.node (.leaf (.ubHLePi 17 2 1 5721605380)) (.leaf (.ubHLePi 17 3 0 1033857826))))
            (.node (.node (.leaf (.ubHGe0 17 0 2 3585858789)) (.leaf (.ubHGe0 17 1 1 4371627590))) (.node (.leaf (.ubHGe0 17 2 0 1231311908)) (.leaf (.ubHLePi 17 0 1 1412547167)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 17 1 0 835449716)) (.leaf (.ubHGe0 17 0 0 244538544))) (.node (.leaf (.ubPHi 9 1051204054)) (.leaf (.ubPHi 8 42510329825))))
            (.node
            (.node (.leaf (.ubPHi 7 33926223773)) (.leaf (.ubPHi 6 373747587355)))
            (.node (.leaf (.ubPHi 5 111718381210)) (.node (.leaf (.ubPHi 4 532865587848)) (.leaf (.ubPHi 3 70087532605)))))))))))))

private lemma cert_47_9_u : checkBinoFarkasU 47 9 cert_47_9 = true := by decide
private lemma cert_47_9_c_5 : checkBinoCForJ 47 9 5 cert_47_9 = true := by decide
private lemma cert_47_9_c_6 : checkBinoCForJ 47 9 6 cert_47_9 = true := by decide
private lemma cert_47_9_c_7 : checkBinoCForJ 47 9 7 cert_47_9 = true := by decide
private lemma cert_47_9_c_8 : checkBinoCForJ 47 9 8 cert_47_9 = true := by decide
private lemma cert_47_9_c_9 : checkBinoCForJ 47 9 9 cert_47_9 = true := by decide
private lemma cert_47_9_c_10 : checkBinoCForJ 47 9 10 cert_47_9 = true := by decide
private lemma cert_47_9_c_11 : checkBinoCForJ 47 9 11 cert_47_9 = true := by decide
private lemma cert_47_9_c_12 : checkBinoCForJ 47 9 12 cert_47_9 = true := by decide
private lemma cert_47_9_c_13 : checkBinoCForJ 47 9 13 cert_47_9 = true := by decide
private lemma cert_47_9_c_17 : checkBinoCForJ 47 9 17 cert_47_9 = true := by decide
private lemma cert_47_9_c_rest :
    ([0, 1, 2, 3, 4, 14, 15, 16, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] : List ℕ).all (fun j => checkBinoCForJ 47 9 j cert_47_9) = true := by
  decide
lemma cert_47_9_c_ok : ∀ j ≤ 47, checkBinoCForJ 47 9 j cert_47_9 = true := by
  have hcov : ∀ j : Fin 48, j.val = 5 ∨ j.val = 6 ∨ j.val = 7 ∨ j.val = 8 ∨ j.val = 9 ∨ j.val = 10 ∨ j.val = 11 ∨ j.val = 12 ∨ j.val = 13 ∨ j.val = 17 ∨ j.val ∈ ([0, 1, 2, 3, 4, 14, 15, 16, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47] : List ℕ) := by decide
  intro j hj
  rcases hcov ⟨j, by omega⟩ with h | h | h | h | h | h | h | h | h | h | h
  · dsimp only at h; rw [h]; exact cert_47_9_c_5
  · dsimp only at h; rw [h]; exact cert_47_9_c_6
  · dsimp only at h; rw [h]; exact cert_47_9_c_7
  · dsimp only at h; rw [h]; exact cert_47_9_c_8
  · dsimp only at h; rw [h]; exact cert_47_9_c_9
  · dsimp only at h; rw [h]; exact cert_47_9_c_10
  · dsimp only at h; rw [h]; exact cert_47_9_c_11
  · dsimp only at h; rw [h]; exact cert_47_9_c_12
  · dsimp only at h; rw [h]; exact cert_47_9_c_13
  · dsimp only at h; rw [h]; exact cert_47_9_c_17
  · exact List.all_eq_true.mp cert_47_9_c_rest j h

/-- **World Record `B_9 ≤ 46`**: Every Boolean function of polynomial degree `≤ 9` has
maximum sensitivity `≤ 46` (kernel-verified via `j`-sliced `by decide`). -/
theorem maxSensitivity_le_fortysix_of_deg_le_nine_proof {m : ℕ} (f : BooleanFun m) (hf : polyDegree f ≤ 9) :
    maxSensitivity f ≤ 46 := by
  have hlt := maxSensitivity_lt_of_bino_farkas_sliced (n := 47) (d := 9) cert_47_9 cert_47_9_u cert_47_9_c_ok f hf
  omega

end DegreeSensitivity
