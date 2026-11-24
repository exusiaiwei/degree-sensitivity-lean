module

public import DegreeSensitivity.IntTrieVerifier

@[expose] public section

/-!
# New World Record: `B_8 ≤ 36` (Impossibility of `(n = 37, d = 8)`)

Small-integer Subset-`J` Terwilliger LP Farkas infeasibility certificate
(1044 pure integer multipliers, ≤ 19 digits, `J = [3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]`),
verified via `j`-sliced depth-8 `by decide` checks.
Strictly beats Wellens (2022) `B_8 ≤ 38`.
-/

namespace DegreeSensitivity

/-- Balanced binary tree of small-integer Farkas multipliers for `(n = 37, d = 8)`. -/
def cert_37_8 : BinTree BinoStep :=
  (.node
    (.node
      (.node
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.eqP0 38802875676034)) (.leaf (.eqP1 42685493671022))) (.node (.leaf (.eqDiag 3 (-36240802684285))) (.leaf (.eqB00 3 (-605128061890548)))))
            (.node (.node (.leaf (.eqB10 3 271896643989498)) (.leaf (.eqB01 3 1351610332569662))) (.node (.leaf (.eqDiag 5 762399619218436)) (.leaf (.eqB00 5 4898749807386467)))))
            (.node
            (.node (.node (.leaf (.eqB10 5 (-6388868186648635))) (.leaf (.eqB01 5 (-10892035171299716)))) (.node (.leaf (.eqDiag 6 (-3531522732846519))) (.leaf (.eqB00 6 (-8743615775250159)))))
            (.node (.node (.leaf (.eqB10 6 21094003522887183)) (.leaf (.eqB01 6 14940006011682944))) (.node (.leaf (.eqDiag 7 8976951244324724)) (.leaf (.eqB00 7 910214101631571))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqB10 7 (-24775377861863955))) (.leaf (.eqB01 7 10801130172821133))) (.node (.leaf (.eqDiag 8 (-15229324057603896))) (.leaf (.eqB00 8 13748054392323889))))
            (.node (.node (.leaf (.eqB10 8 (-1805613021210571))) (.leaf (.eqB01 8 (-40750129238928539)))) (.node (.leaf (.eqDiag 9 18372659791571356)) (.leaf (.eqB00 9 (-19288994528686050))))))
            (.node
            (.node (.node (.leaf (.eqB10 9 32735617804967993)) (.leaf (.eqB01 9 38392502158944932))) (.node (.leaf (.eqDiag 10 (-16105251812072821))) (.leaf (.eqB00 10 13898541045738089))))
            (.node (.node (.leaf (.eqB10 10 (-29243657941906781))) (.leaf (.eqB01 10 (-21851001263384827)))) (.node (.leaf (.eqDiag 11 10243269948266633)) (.leaf (.eqB00 11 (-7339853603698896))))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.eqB10 11 4320276183029145)) (.leaf (.eqB01 11 16762725852432649))) (.node (.leaf (.eqDiag 12 (-4622847359461575))) (.leaf (.eqB00 12 3660395057122177))))
            (.node (.node (.leaf (.eqB10 12 6880363627629616)) (.leaf (.eqB01 12 (-13769270906744758)))) (.node (.leaf (.eqDiag 13 1407021661842713)) (.leaf (.eqB00 13 (-1588539612670724))))))
            (.node
            (.node (.node (.leaf (.eqB10 13 (-3158308884426084))) (.leaf (.eqB01 13 6090312252993389))) (.node (.leaf (.eqDiag 14 (-259352410533150))) (.leaf (.eqB00 14 466419106795686))))
            (.node (.node (.leaf (.eqB10 14 (-159310111685875))) (.leaf (.eqB01 14 (-1020223130634174)))) (.node (.leaf (.eqDiag 15 21870150070357)) (.leaf (.eqB00 15 (-70116365067438)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqB10 15 227805849553212)) (.leaf (.eqB01 15 3379728376012))) (.node (.leaf (.eqSym 3 5 0 16841024566279062)) (.leaf (.eqSym 3 5 1 7538351674095843))))
            (.node (.node (.leaf (.eqSym 3 5 2 25543125839857114)) (.leaf (.eqSym 3 5 3 (-2789480376037987)))) (.node (.leaf (.eqSym 3 6 0 (-29090613161088167))) (.leaf (.eqSym 3 6 1 (-11884230403239347))))))
            (.node
            (.node (.node (.leaf (.eqSym 3 6 2 (-105236539238956420))) (.leaf (.eqSym 3 6 3 6050109839780696))) (.node (.leaf (.eqSym 3 7 0 (-20691574873230488))) (.leaf (.eqSym 3 7 2 136602568298517811))))
            (.node
            (.node (.leaf (.eqSym 3 8 0 93441020308402126)) (.leaf (.eqSym 3 8 1 5471031764182552)))
            (.node (.leaf (.eqSym 3 9 0 (-87269948593127423))) (.node (.leaf (.eqSym 3 9 2 (-157942639323784924))) (.leaf (.eqSym 3 9 3 (-16169916586726774))))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 3 10 0 26782965507661539)) (.leaf (.eqSym 3 10 2 152601687245571417))) (.node (.leaf (.eqSym 3 11 2 (-63042801746341945))) (.leaf (.eqSym 3 11 3 49808128847715083))))
            (.node (.node (.leaf (.eqSym 3 12 0 2834293837952902)) (.leaf (.eqSym 3 12 2 11918188819737135))) (.node (.leaf (.eqSym 3 12 3 (-57554187779075785))) (.leaf (.eqSym 3 13 0 (-2110548382005810))))))
            (.node
            (.node (.node (.leaf (.eqSym 3 13 1 (-1468910720715692))) (.leaf (.eqSym 3 13 3 21727739528678463))) (.node (.leaf (.eqSym 3 15 1 615553226258152)) (.leaf (.eqSym 3 15 2 (-440386213957885)))))
            (.node (.node (.leaf (.eqSym 3 15 3 (-1108498187040123))) (.leaf (.eqSym 5 6 0 109693279390294036))) (.node (.leaf (.eqSym 5 6 1 (-175641714711142076))) (.leaf (.eqSym 5 6 2 421513411003388915))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 5 6 3 14871408245351340)) (.leaf (.eqSym 5 6 4 50783213574406539))) (.node (.leaf (.eqSym 5 6 5 (-3609639873004807))) (.leaf (.eqSym 5 7 0 (-96014067878334879)))))
            (.node (.node (.leaf (.eqSym 5 7 1 352282092821832835)) (.leaf (.eqSym 5 7 2 (-736283311996749200)))) (.node (.leaf (.eqSym 5 7 4 (-162655450607833918))) (.leaf (.eqSym 5 8 0 (-242700064264963196))))))
            (.node
            (.node (.node (.leaf (.eqSym 5 8 1 13415853290600468)) (.leaf (.eqSym 5 8 2 (-40396829246887214)))) (.node (.leaf (.eqSym 5 8 3 12051416353652740)) (.leaf (.eqSym 5 8 4 (-117007142751369673)))))
            (.node (.node (.leaf (.eqSym 5 8 5 78813210399651362)) (.leaf (.eqSym 5 9 0 386760433896302110))) (.node (.leaf (.eqSym 5 9 1 (-373234721402882360))) (.leaf (.eqSym 5 9 2 914217847533846957)))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 5 9 3 (-179741015947683576))) (.leaf (.eqSym 5 9 4 730410386738339693))) (.node (.leaf (.eqSym 5 9 5 (-151102720767784189))) (.leaf (.eqSym 5 10 0 (-49864731896551195)))))
            (.node (.node (.leaf (.eqSym 5 10 1 150925851512559038)) (.leaf (.eqSym 5 10 2 (-506854250029609664)))) (.node (.leaf (.eqSym 5 10 4 (-383639769311911584))) (.leaf (.eqSym 5 10 5 38138428980179451)))))
            (.node
            (.node (.node (.leaf (.eqSym 5 11 0 (-166099589639863264))) (.leaf (.eqSym 5 11 1 (-168517297228636390)))) (.node (.leaf (.eqSym 5 11 3 327541356464280533)) (.leaf (.eqSym 5 11 4 (-608620112120468499)))))
            (.node (.node (.leaf (.eqSym 5 11 5 61781488692912749)) (.leaf (.eqSym 5 12 0 53629935378457633))) (.node (.leaf (.eqSym 5 12 1 519744323423049299)) (.leaf (.eqSym 5 12 2 (-357698794437938632)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 5 12 4 598808612068820985)) (.leaf (.eqSym 5 12 5 30001674947816525))) (.node (.leaf (.eqSym 5 13 0 3871374383103664)) (.leaf (.eqSym 5 13 1 (-365373963319240483)))))
            (.node (.node (.leaf (.eqSym 5 13 2 404000830004385853)) (.leaf (.eqSym 5 13 3 (-241697096455131533)))) (.node (.leaf (.eqSym 5 13 4 (-81532864532069073))) (.leaf (.eqSym 5 13 5 (-66393965835847323))))))
            (.node
            (.node (.node (.leaf (.eqSym 5 14 0 27375983555204604)) (.leaf (.eqSym 5 15 0 (-15804298468885068)))) (.node (.leaf (.eqSym 5 15 1 47548323615277553)) (.leaf (.eqSym 5 15 2 (-72955776990579901)))))
            (.node
            (.node (.leaf (.eqSym 5 15 3 64184307367999092)) (.leaf (.eqSym 5 15 4 (-26554863439096508))))
            (.node (.leaf (.eqSym 5 15 5 13132769863337239)) (.node (.leaf (.eqSym 6 7 0 158935065390071131)) (.leaf (.eqSym 6 7 1 (-360459179589107840)))))))))))
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 6 7 2 580220400164743283)) (.leaf (.eqSym 6 7 3 117641217585769527))) (.node (.leaf (.eqSym 6 7 4 186463424780347572)) (.leaf (.eqSym 6 7 5 56595777662131998))))
            (.node (.node (.leaf (.eqSym 6 7 6 12299112017131448)) (.leaf (.eqSym 6 8 0 219499768692320756))) (.node (.leaf (.eqSym 6 8 1 (-12698878406331647))) (.leaf (.eqSym 6 8 3 418635901298442715)))))
            (.node
            (.node (.node (.leaf (.eqSym 6 8 6 (-101986289110060354))) (.leaf (.eqSym 6 9 0 (-508478212775822286)))) (.node (.leaf (.eqSym 6 9 1 242206629994324014)) (.leaf (.eqSym 6 9 2 (-281578273487008995)))))
            (.node (.node (.leaf (.eqSym 6 9 3 (-1285165308611138186))) (.leaf (.eqSym 6 9 4 (-331039637052170212)))) (.node (.leaf (.eqSym 6 9 5 (-371656743784859745))) (.leaf (.eqSym 6 9 6 127832192060824342))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 6 10 3 618334585745927302)) (.leaf (.eqSym 6 10 5 417331933691666405))) (.node (.leaf (.eqSym 6 11 0 607765499300536685)) (.leaf (.eqSym 6 11 3 815051949050194363))))
            (.node (.node (.leaf (.eqSym 6 11 4 513756022299293929)) (.leaf (.eqSym 6 11 6 71061559510850257))) (.node (.leaf (.eqSym 6 12 0 (-659071453166158329))) (.leaf (.eqSym 6 12 3 (-1106441628792532633))))))
            (.node
            (.node (.node (.leaf (.eqSym 6 12 4 (-350884956179240625))) (.leaf (.eqSym 6 12 5 (-115194128686191019)))) (.node (.leaf (.eqSym 6 12 6 (-294344067132550041))) (.leaf (.eqSym 6 13 0 355814468432014548))))
            (.node (.node (.leaf (.eqSym 6 13 1 (-42195845252799249))) (.leaf (.eqSym 6 13 3 506359753230819173))) (.node (.leaf (.eqSym 6 13 6 209339854599422304)) (.leaf (.eqSym 6 14 0 (-96727520721505549))))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 6 14 3 15450781948363146)) (.leaf (.eqSym 6 14 6 (-3156686427537659)))) (.node (.leaf (.eqSym 6 15 0 9061831404680933)) (.leaf (.eqSym 6 15 1 6714598250814810))))
            (.node (.node (.leaf (.eqSym 6 15 2 17635264779328161)) (.leaf (.eqSym 6 15 3 (-78945714505803849)))) (.node (.leaf (.eqSym 6 15 4 32488807968395403)) (.leaf (.eqSym 6 15 5 9313667614093332)))))
            (.node
            (.node (.node (.leaf (.eqSym 6 15 6 (-24576842797112491))) (.leaf (.eqSym 7 8 3 (-688808497060539608)))) (.node (.leaf (.eqSym 7 8 4 (-2210646141692818))) (.leaf (.eqSym 7 8 5 83472733188743035))))
            (.node (.node (.leaf (.eqSym 7 8 6 17519996758528242)) (.leaf (.eqSym 7 8 7 60404508479174856))) (.node (.leaf (.eqSym 7 9 0 171858340217276320)) (.leaf (.eqSym 7 9 1 51449377408868536))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 7 9 2 (-383778781851259279))) (.leaf (.eqSym 7 9 3 1902565044142762655))) (.node (.leaf (.eqSym 7 9 4 (-27051402894769529))) (.leaf (.eqSym 7 9 5 196237930391748292))))
            (.node (.node (.leaf (.eqSym 7 9 6 29662557522523598)) (.leaf (.eqSym 7 9 7 (-47305411994716657)))) (.node (.leaf (.eqSym 7 10 0 19109730136621194)) (.leaf (.eqSym 7 10 5 (-381694872585285416))))))
            (.node
            (.node (.node (.leaf (.eqSym 7 10 6 21962352738502715)) (.leaf (.eqSym 7 10 7 (-89076426408306468)))) (.node (.leaf (.eqSym 7 11 0 (-707871003042507019))) (.leaf (.eqSym 7 11 1 333023492692784245))))
            (.node
            (.node (.leaf (.eqSym 7 11 2 450262158864192233)) (.leaf (.eqSym 7 11 3 (-2884776614943834460))))
            (.node (.leaf (.eqSym 7 11 5 164041389489834010)) (.node (.leaf (.eqSym 7 11 6 (-59078556492754884))) (.leaf (.eqSym 7 12 0 1084618280940043068)))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 7 12 1 (-904584431344516193))) (.leaf (.eqSym 7 12 3 2785505732532104163))) (.node (.leaf (.eqSym 7 12 6 (-91223432276499732))) (.leaf (.eqSym 7 12 7 257245015628772982))))
            (.node (.node (.leaf (.eqSym 7 13 0 (-653485706903154389))) (.leaf (.eqSym 7 13 1 507493126333747837))) (.node (.leaf (.eqSym 7 13 3 (-1176185282490923784))) (.leaf (.eqSym 7 13 4 135297010912291386)))))
            (.node
            (.node (.node (.leaf (.eqSym 7 13 6 96410799169655833)) (.leaf (.eqSym 7 13 7 (-196772845077148693)))) (.node (.leaf (.eqSym 7 14 0 144751310223921918)) (.leaf (.eqSym 7 14 1 (-10190172008032885)))))
            (.node (.node (.leaf (.eqSym 7 14 4 (-41194764519326909))) (.leaf (.eqSym 7 14 6 17427808396123830))) (.node (.leaf (.eqSym 7 15 0 (-5040549147741223))) (.leaf (.eqSym 7 15 1 (-10143857711990501)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 7 15 2 (-85943952858625388))) (.leaf (.eqSym 7 15 3 179340835406200563))) (.node (.leaf (.eqSym 7 15 4 (-41032223183988477))) (.leaf (.eqSym 7 15 5 (-5454811748366726)))))
            (.node (.node (.leaf (.eqSym 7 15 6 (-20382401104977018))) (.leaf (.eqSym 7 15 7 24481317675296667))) (.node (.leaf (.eqSym 8 9 0 78029245516571477)) (.leaf (.eqSym 8 9 2 (-27762982792960950))))))
            (.node
            (.node (.node (.leaf (.eqSym 8 9 3 (-824030198748788248))) (.leaf (.eqSym 8 9 7 56121383017320584))) (.node (.leaf (.eqSym 8 9 8 (-4059319841326758))) (.leaf (.eqSym 8 10 5 196225796077011343))))
            (.node
            (.node (.leaf (.eqSym 8 11 3 1599314639407744722)) (.leaf (.eqSym 8 11 4 (-148568840061371947))))
            (.node (.leaf (.eqSym 8 11 6 (-206513353972364199))) (.node (.leaf (.eqSym 8 11 8 (-47574296832536466))) (.leaf (.eqSym 8 12 0 (-145920499339401856)))))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 8 12 3 (-1539691591099330656))) (.leaf (.eqSym 8 12 6 41641100406180068))) (.node (.leaf (.eqSym 8 12 7 95592856834992645)) (.leaf (.eqSym 8 12 8 38842047117349007))))
            (.node (.node (.leaf (.eqSym 8 13 0 186904643150513614)) (.leaf (.eqSym 8 13 1 (-3792000447540272)))) (.node (.leaf (.eqSym 8 13 3 534490858888268170)) (.leaf (.eqSym 8 13 6 80405682923198570)))))
            (.node
            (.node (.node (.leaf (.eqSym 8 13 7 (-104048613896422811))) (.leaf (.eqSym 8 14 0 (-90232266028100552)))) (.node (.leaf (.eqSym 8 15 0 14457267903313229)) (.leaf (.eqSym 8 15 1 8174394074781073))))
            (.node (.node (.leaf (.eqSym 8 15 2 (-12633715275826631))) (.leaf (.eqSym 8 15 3 (-28204887856338143)))) (.node (.leaf (.eqSym 8 15 4 29351051168309456)) (.leaf (.eqSym 8 15 5 (-33939852488616946)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 8 15 7 12738882523284437)) (.leaf (.eqSym 8 15 8 (-2437754501089678)))) (.node (.leaf (.eqSym 9 10 1 (-21925291075956889))) (.leaf (.eqSym 9 10 4 (-326170021056887193)))))
            (.node (.node (.leaf (.eqSym 9 10 5 (-163580512330692839))) (.leaf (.eqSym 9 10 9 57541961113680749))) (.node (.leaf (.eqSym 9 11 0 314616151436606897)) (.leaf (.eqSym 9 11 1 (-120794508933804045))))))
            (.node
            (.node (.node (.leaf (.eqSym 9 11 3 (-2381042981443801042))) (.leaf (.eqSym 9 11 4 4846453051961581815))) (.node (.leaf (.eqSym 9 11 5 (-3651427734343047480))) (.leaf (.eqSym 9 11 6 1771217883727741631))))
            (.node
            (.node (.leaf (.eqSym 9 11 8 (-109929451069573676))) (.leaf (.eqSym 9 12 0 (-318175589168619544))))
            (.node (.leaf (.eqSym 9 12 1 (-675699140404277900))) (.node (.leaf (.eqSym 9 12 2 3077937316391148164)) (.leaf (.eqSym 9 12 3 (-2437791529627162621))))))))))))
      (.node
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 9 12 5 910468227871640132)) (.leaf (.eqSym 9 12 6 (-835249811624922183)))) (.node (.leaf (.eqSym 9 12 9 (-79749150092605197))) (.leaf (.eqSym 9 13 0 154029136785362716))))
            (.node (.node (.leaf (.eqSym 9 13 3 (-2570324562435413969))) (.leaf (.eqSym 9 13 4 6169560635733439023))) (.node (.leaf (.eqSym 9 13 5 (-7973719027451899199))) (.leaf (.eqSym 9 13 6 6644825938979347276)))))
            (.node
            (.node (.node (.leaf (.eqSym 9 13 7 (-3428680608932029415))) (.leaf (.eqSym 9 13 8 1043408505133393423))) (.node (.leaf (.eqSym 9 13 9 (-54515539987679792))) (.leaf (.eqSym 9 14 0 27599392039204339))))
            (.node (.node (.leaf (.eqSym 9 14 1 (-54274771992356836))) (.leaf (.eqSym 9 14 3 127310420530998361))) (.node (.leaf (.eqSym 9 14 7 (-10919389958005051))) (.leaf (.eqSym 9 14 9 (-10345668310331261)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 9 15 0 (-34321520049331676))) (.leaf (.eqSym 9 15 1 72155079633595014))) (.node (.leaf (.eqSym 9 15 3 (-175184417504930686))) (.leaf (.eqSym 9 15 4 234213290848716357))))
            (.node (.node (.leaf (.eqSym 9 15 6 (-388807586770082954))) (.leaf (.eqSym 9 15 7 433631483623373382))) (.node (.leaf (.eqSym 9 15 8 (-183842837327067666))) (.leaf (.eqSym 9 15 9 21696986542885483)))))
            (.node
            (.node (.node (.leaf (.eqSym 10 11 0 10261136428311215)) (.leaf (.eqSym 10 11 1 (-30382125708546627)))) (.node (.leaf (.eqSym 10 11 5 (-618813731345589313))) (.leaf (.eqSym 10 11 8 (-419731388563323003)))))
            (.node (.node (.leaf (.eqSym 10 11 9 329357244687143391)) (.leaf (.eqSym 10 11 10 (-30368593264291394)))) (.node (.leaf (.eqSym 10 12 5 60658147318371706)) (.leaf (.eqSym 10 12 7 779221458183179202)))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 10 12 9 (-209610887689544243))) (.leaf (.eqSym 10 13 5 468415805039380859))) (.node (.leaf (.eqSym 10 13 7 (-1002778931676986784))) (.leaf (.eqSym 10 13 8 519296831243979091))))
            (.node (.node (.leaf (.eqSym 10 13 9 (-76707691658608621))) (.leaf (.eqSym 10 14 0 (-59498553623494443)))) (.node (.leaf (.eqSym 10 14 1 288787331812269583)) (.leaf (.eqSym 10 14 2 (-570352392491537465))))))
            (.node
            (.node (.node (.leaf (.eqSym 10 14 3 663882981772464846)) (.leaf (.eqSym 10 14 4 (-578296368829518697)))) (.node (.leaf (.eqSym 10 14 6 188204416300500653)) (.leaf (.eqSym 10 14 8 (-37233922627766459)))))
            (.node (.node (.leaf (.eqSym 10 14 10 20435150632620564)) (.leaf (.eqSym 10 15 0 37279947108087795))) (.node (.leaf (.eqSym 10 15 1 (-159966637450881550))) (.leaf (.eqSym 10 15 2 229448563452962642))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 10 15 3 (-100922082456536282))) (.leaf (.eqSym 10 15 5 (-3186873809496236)))) (.node (.leaf (.eqSym 10 15 6 34490323279429473)) (.leaf (.eqSym 10 15 8 (-4485009437070734)))))
            (.node (.node (.leaf (.eqSym 10 15 10 (-4557364878098476))) (.leaf (.eqSym 11 12 0 81517443601414763))) (.node (.leaf (.eqSym 11 12 1 638208537980494757)) (.leaf (.eqSym 11 12 2 (-1162897161763971913))))))
            (.node
            (.node (.node (.leaf (.eqSym 11 12 5 2055393855374870013)) (.leaf (.eqSym 11 12 6 (-1882973057715635253)))) (.node (.leaf (.eqSym 11 12 10 103166971162138325)) (.leaf (.eqSym 11 12 11 25345521025684601))))
            (.node
            (.node (.leaf (.eqSym 11 13 0 (-118524051284522514))) (.leaf (.eqSym 11 13 2 (-579919811477740860))))
            (.node (.leaf (.eqSym 11 13 3 1511811996166787467)) (.node (.leaf (.eqSym 11 13 5 (-2732338494951011436))) (.leaf (.eqSym 11 13 6 1953393328204517581)))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 11 13 10 (-46591286186104890))) (.leaf (.eqSym 11 13 11 (-30068227972148468)))) (.node (.leaf (.eqSym 11 14 0 25451200910823110)) (.leaf (.eqSym 11 14 3 68053416730868649))))
            (.node (.node (.leaf (.eqSym 11 14 9 (-23810223961047915))) (.leaf (.eqSym 11 14 10 (-4120697224366872)))) (.node (.leaf (.eqSym 11 15 0 39050226426488005)) (.leaf (.eqSym 11 15 1 (-256710145810847075))))))
            (.node
            (.node (.node (.leaf (.eqSym 11 15 2 693140358653589489)) (.leaf (.eqSym 11 15 3 (-795355450618031365)))) (.node (.leaf (.eqSym 11 15 5 662767392933710262)) (.leaf (.eqSym 11 15 6 (-375898847094614636)))))
            (.node (.node (.leaf (.eqSym 11 15 10 13629891338863088)) (.leaf (.eqSym 11 15 11 4425986779211504))) (.node (.leaf (.eqSym 12 13 0 19014309231782559)) (.leaf (.eqSym 12 13 1 165342304924168105))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 12 13 4 (-1196006446072467166))) (.leaf (.eqSym 12 13 5 2023245181382554240))) (.node (.leaf (.eqSym 12 13 6 (-972133218876626612))) (.leaf (.eqSym 12 13 9 (-4732680811873524)))))
            (.node (.node (.leaf (.eqSym 12 13 10 (-13737834730908635))) (.leaf (.eqSym 12 13 11 4628072465083240))) (.node (.leaf (.eqSym 12 13 12 20280765505518810)) (.leaf (.eqSym 12 14 1 (-62516170122468087))))))
            (.node
            (.node (.node (.leaf (.eqSym 12 14 6 71257080034737008)) (.leaf (.eqSym 12 14 8 (-75031123881656722)))) (.node (.leaf (.eqSym 12 14 11 71956732170075931)) (.leaf (.eqSym 12 14 12 (-36427842419811427)))))
            (.node (.node (.leaf (.eqSym 12 15 0 (-231154750830294))) (.leaf (.eqSym 12 15 1 7207074979863347))) (.node (.leaf (.eqSym 12 15 2 (-35751870178640934))) (.leaf (.eqSym 12 15 3 75418996649872768)))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 12 15 6 (-82067969373871882))) (.leaf (.eqSym 12 15 9 79409325549380436))) (.node (.leaf (.eqSym 12 15 11 (-57161813756027588))) (.leaf (.eqSym 12 15 12 17736859317996026))))
            (.node (.node (.leaf (.eqSym 13 14 0 (-7424515112340710))) (.leaf (.eqSym 13 14 1 37618436505359669))) (.node (.leaf (.eqSym 13 14 4 (-87137934048953901))) (.leaf (.eqSym 13 14 5 192228626967366997)))))
            (.node
            (.node (.node (.leaf (.eqSym 13 14 6 (-171077920783131562))) (.leaf (.eqSym 13 14 9 86727642179781427))) (.node (.leaf (.eqSym 13 14 11 (-56712765623274913))) (.leaf (.eqSym 13 14 13 13439049793694712))))
            (.node (.node (.leaf (.eqSym 13 15 0 (-583013638561026))) (.leaf (.eqSym 13 15 3 (-13298964208514564)))) (.node (.leaf (.eqSym 13 15 7 71936148326660466)) (.leaf (.eqSym 13 15 8 (-80621018518802370)))))))
            (.node
            (.node
            (.node (.node (.leaf (.eqSym 13 15 10 75651680759990379)) (.leaf (.eqSym 13 15 11 (-121026342708988264)))) (.node (.leaf (.eqSym 13 15 12 91500069933975725)) (.leaf (.eqSym 13 15 13 (-24933110081777674)))))
            (.node (.node (.leaf (.eqSym 14 15 0 (-2842767473695502))) (.leaf (.eqSym 14 15 1 8690895735563650))) (.node (.leaf (.eqSym 14 15 3 (-13101896699183923))) (.leaf (.eqSym 14 15 5 15441629682285595)))))
            (.node
            (.node (.node (.leaf (.eqSym 14 15 9 (-68143645110783288))) (.leaf (.eqSym 14 15 10 90444948279791720))) (.node (.leaf (.eqSym 14 15 12 (-54563539525411612))) (.leaf (.eqSym 14 15 13 27716260382308217))))
            (.node
            (.node (.leaf (.eqSym 14 15 14 (-3337780023583853))) (.leaf (.ubPHi 2 18741573962982)))
            (.node (.leaf (.ubPLo 37 224820635196)) (.node (.leaf (.ubHLePj 3 0 2 9603198448536)) (.leaf (.ubHMcc 3 0 26 127588509549))))))))))
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 3 0 32 161656957639)) (.leaf (.ubHLePi 3 0 33 225792938746))) (.node (.leaf (.ubHLePj 3 1 1 719123162485)) (.leaf (.ubHMcc 3 1 34 618019754494))))
            (.node (.node (.leaf (.ubHMcc 3 2 0 3711432017217)) (.leaf (.ubHLePj 3 2 34 507751374914))) (.node (.leaf (.ubHGe0 3 3 34 136089977860)) (.leaf (.ubHLePj 5 0 25 276371464696)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 5 0 30 498182829938)) (.leaf (.ubHGe0 5 0 31 293441033389))) (.node (.leaf (.ubHLePi 5 1 31 237154387394)) (.leaf (.ubHLePj 5 1 32 498331641930))))
            (.node (.node (.leaf (.ubHLePj 5 3 23 153494769296)) (.leaf (.ubHGe0 5 3 32 9899275878))) (.node (.leaf (.ubHLePj 5 4 0 8445236718081)) (.leaf (.ubHGe0 5 4 27 180029697334))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHMcc 5 4 32 274825838710)) (.leaf (.ubHLePj 5 5 7 931169216532))) (.node (.leaf (.ubHLePj 5 5 20 125453893346)) (.leaf (.ubHLePi 5 5 32 96588847549))))
            (.node (.node (.leaf (.ubHGe0 6 0 6 817511580942)) (.leaf (.ubHLePj 6 0 12 357825692161))) (.node (.leaf (.ubHLePi 6 0 31 69595389546)) (.leaf (.ubHLePj 6 1 1 88982932466)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 6 1 5 576637353508)) (.leaf (.ubHLePj 6 1 11 1537025339645))) (.node (.leaf (.ubHGe0 6 1 30 315959312930)) (.leaf (.ubHGe0 6 2 17 519692629954))))
            (.node (.node (.leaf (.ubHGe0 6 3 16 18864909522)) (.leaf (.ubHGe0 6 4 1 551976782449))) (.node (.leaf (.ubHLePj 6 4 22 103734426308)) (.leaf (.ubHGe0 6 5 13 25197087673)))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 6 5 14 121172758106)) (.leaf (.ubHGe0 6 6 12 701092043104))) (.node (.leaf (.ubHLePj 6 6 19 374385389600)) (.leaf (.ubHGe0 6 6 25 430777425359))))
            (.node (.node (.leaf (.ubHLePj 6 6 29 402030264537)) (.leaf (.ubHLePj 7 0 27 364488498600))) (.node (.leaf (.ubHLePj 7 2 0 310201855721)) (.leaf (.ubHGe0 7 2 30 77889651392)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 7 5 0 6591074586555)) (.leaf (.ubHGe0 7 6 12 12693971136))) (.node (.leaf (.ubHLePj 7 7 3 990466138124)) (.leaf (.ubHGe0 7 7 30 197524886087))))
            (.node (.node (.leaf (.ubHGe0 8 0 19 132739991685)) (.leaf (.ubHLePj 8 0 27 391426250808))) (.node (.leaf (.ubHGe0 8 2 29 131178099634)) (.leaf (.ubHLePi 8 6 25 45322992947))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePj 8 6 29 232968460503)) (.leaf (.ubHGe0 9 0 19 256643088225))) (.node (.leaf (.ubHGe0 9 4 28 98602346305)) (.leaf (.ubHLePi 9 7 0 2339976949657))))
            (.node (.node (.leaf (.ubHLePi 9 9 10 95701191421)) (.leaf (.ubHLePi 9 9 28 26315754525))) (.node (.leaf (.ubHLePi 10 2 17 83604332755)) (.leaf (.ubHGe0 10 5 27 43561062916)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 10 6 26 24728582752)) (.leaf (.ubHLePi 10 8 23 197102697370))) (.node (.leaf (.ubHLePi 10 9 0 635039223970)) (.leaf (.ubHMcc 10 9 26 233215638107))))
            (.node
            (.node (.leaf (.ubHLePi 10 10 8 654421197500)) (.leaf (.ubHMcc 10 10 15 114121246728)))
            (.node (.leaf (.ubHLePi 10 10 21 45539773782)) (.node (.leaf (.ubHMcc 10 10 26 38570513892)) (.leaf (.ubHLePi 10 10 27 104824961888)))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHMcc 11 0 2 2849888184964)) (.leaf (.ubHMcc 11 0 23 1275717066886))) (.node (.leaf (.ubHMcc 11 0 24 89931974473)) (.leaf (.ubHLePi 11 3 3 1609488277807))))
            (.node (.node (.leaf (.ubHLePi 11 4 25 391528298824)) (.leaf (.ubHLePi 11 5 14 896940744093))) (.node (.leaf (.ubHLePi 11 7 12 193441044772)) (.leaf (.ubHMcc 11 7 19 256746294258)))))
            (.node
            (.node (.node (.leaf (.ubHMcc 11 7 20 481340438010)) (.leaf (.ubHMcc 11 8 26 1520683198))) (.node (.leaf (.ubHMcc 11 11 13 291201597997)) (.leaf (.ubHLePi 11 11 20 259843912356))))
            (.node (.node (.leaf (.ubHMcc 11 11 24 300951806704)) (.leaf (.ubHLePi 11 11 26 115315447855))) (.node (.leaf (.ubHLePi 12 0 25 20845191803)) (.leaf (.ubHMcc 12 1 1 2132222699529))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 12 1 21 11832258496)) (.leaf (.ubHLePi 12 1 25 78135502140))) (.node (.leaf (.ubHMcc 12 2 0 1224837956530)) (.leaf (.ubHMcc 12 3 9 83795213605))))
            (.node (.node (.leaf (.ubHMcc 12 4 8 1176352135917)) (.leaf (.ubHLePi 12 5 14 9155846157))) (.node (.leaf (.ubHMcc 12 8 1 201616678105)) (.leaf (.ubHMcc 12 9 0 1904307533359)))))
            (.node
            (.node (.node (.leaf (.ubHMcc 12 9 25 125779301901)) (.leaf (.ubHLePi 12 10 22 376987023731))) (.node (.leaf (.ubHLePi 12 12 3 457662436203)) (.leaf (.ubHLePi 13 0 20 1987434164946))))
            (.node
            (.node (.leaf (.ubHLePi 13 0 21 93422990878)) (.leaf (.ubHMcc 13 1 1 4407893640790)))
            (.node (.leaf (.ubHLePj 13 1 24 32146312129)) (.node (.leaf (.ubHLePi 13 7 24 6212486414)) (.leaf (.ubHLePi 13 8 23 131166146621))))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHMcc 13 11 24 70358729661)) (.leaf (.ubHGe0 13 12 7 136683156795))) (.node (.leaf (.ubHGe0 13 13 6 328646331226)) (.leaf (.ubHLePi 13 13 24 3407405200))))
            (.node (.node (.leaf (.ubHMcc 14 0 12 4967070409)) (.leaf (.ubHMcc 14 4 22 461198859661))) (.node (.leaf (.ubHMcc 14 5 21 85278204874)) (.leaf (.ubHLePi 14 9 23 48437195628)))))
            (.node
            (.node (.node (.leaf (.ubHMcc 14 12 14 161230552709)) (.leaf (.ubHGe0 14 14 4 65175844199))) (.node (.leaf (.ubHLePj 14 14 11 370069256309)) (.leaf (.ubHGe0 14 14 17 143699018805))))
            (.node (.node (.leaf (.ubHLePi 14 14 23 23039563673)) (.leaf (.ubHMcc 15 0 2 870298762058))) (.node (.leaf (.ubHGe0 15 0 18 932932164372)) (.leaf (.ubHLePj 15 1 1 2549302942739))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 15 1 17 193922823778)) (.leaf (.ubHLePj 15 2 0 209607106893))) (.node (.leaf (.ubHLePi 15 2 17 30254641501)) (.leaf (.ubHMcc 15 3 22 4515183854))))
            (.node (.node (.leaf (.ubHLePj 15 4 21 523218333238)) (.leaf (.ubHMcc 15 4 22 170120476787))) (.node (.leaf (.ubHGe0 15 5 14 29977353597)) (.leaf (.ubHGe0 15 10 9 5808487980)))))
            (.node
            (.node (.node (.leaf (.ubHLePj 15 10 16 15061456783)) (.leaf (.ubHGe0 15 10 21 183164384533))) (.node (.leaf (.ubHLePi 15 10 22 108667863890)) (.leaf (.ubHLePj 15 11 15 86631187686))))
            (.node
            (.node (.leaf (.ubHGe0 15 12 20 16534057092)) (.leaf (.ubHLePi 15 13 5 140167732459)))
            (.node (.leaf (.ubHMcc 15 14 11 35195422887)) (.node (.leaf (.ubHMcc 15 14 12 44289865135)) (.leaf (.ubHLePi 15 14 17 75154100053))))))))))))
    (.node
      (.node
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHMcc 15 15 11 80380141029)) (.leaf (.ubHLePi 15 15 17 27067069204))) (.node (.leaf (.ubHGe0 15 15 22 11306106942)) (.leaf (.ubHLePi 3 0 8 5253189))))
            (.node (.node (.leaf (.ubHLePi 3 1 7 3565876)) (.leaf (.ubHLePi 3 2 6 1288982))) (.node (.leaf (.ubHLePi 3 3 5 81806)) (.leaf (.ubHGe0 3 0 7 43938968)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 3 1 6 26648224)) (.leaf (.ubHGe0 3 2 5 7712590))) (.node (.leaf (.ubHGe0 3 3 4 395305)) (.leaf (.ubHLePi 3 0 6 161322499))))
            (.node (.node (.leaf (.ubHLePi 3 1 5 84901927)) (.leaf (.ubHLePi 3 2 4 19231566))) (.node (.leaf (.ubHLePi 3 3 3 764976)) (.leaf (.ubHGe0 3 0 5 339296262))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 3 1 4 149609231)) (.leaf (.ubHGe0 3 2 3 25579646))) (.node (.leaf (.ubHGe0 3 3 2 740970)) (.leaf (.ubHLePi 3 0 4 446802488))))
            (.node (.node (.leaf (.ubHLePi 3 1 3 157574260)) (.leaf (.ubHLePi 3 2 2 19140729))) (.node (.leaf (.ubHLePi 3 3 1 359219)) (.leaf (.ubHGe0 3 0 3 377009416)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 3 1 2 99246906)) (.leaf (.ubHGe0 3 2 1 7639727))) (.node (.leaf (.ubHGe0 3 3 0 69724)) (.leaf (.ubHLePi 3 0 2 198967774))))
            (.node (.node (.leaf (.ubHLePi 3 1 1 34626519)) (.leaf (.ubHLePi 3 2 0 1270686))) (.node (.leaf (.ubHGe0 3 0 1 60023651)) (.leaf (.ubHGe0 3 1 0 5164222)))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 3 0 0 7922348)) (.leaf (.ubHGe0 5 0 8 1991006))) (.node (.leaf (.ubHLePi 5 1 7 3815193)) (.leaf (.ubHLePi 5 2 6 2591661))))
            (.node (.node (.leaf (.ubHLePi 5 3 5 777660)) (.leaf (.ubHLePi 5 4 4 86191))) (.node (.leaf (.ubHLePi 5 5 3 2837)) (.leaf (.ubHLePi 5 0 7 11348212)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 5 1 6 30866917)) (.leaf (.ubHGe0 5 2 5 17287654))) (.node (.leaf (.ubHGe0 5 3 4 4084620)) (.leaf (.ubHGe0 5 4 3 345597))))
            (.node (.node (.leaf (.ubHGe0 5 5 2 8160)) (.leaf (.ubHGe0 5 0 6 22361341))) (.node (.leaf (.ubHLePi 5 1 5 106454883)) (.leaf (.ubHLePi 5 2 4 47749220))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 5 3 3 8560196)) (.leaf (.ubHLePi 5 4 2 519589))) (.node (.leaf (.ubHLePi 5 5 1 7844)) (.leaf (.ubHLePi 5 0 5 6878572))))
            (.node (.node (.leaf (.ubHGe0 5 1 4 202886346)) (.leaf (.ubHGe0 5 2 3 69953470))) (.node (.leaf (.ubHGe0 5 3 2 8949659)) (.leaf (.ubHGe0 5 4 1 347148)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 5 5 0 2519)) (.leaf (.ubHLePi 5 0 4 43206620))) (.node (.leaf (.ubHLePi 5 1 3 230804390)) (.leaf (.ubHLePi 5 2 2 57366733))))
            (.node
            (.node (.leaf (.ubHLePi 5 3 1 4668896)) (.leaf (.ubHLePi 5 4 0 86966)))
            (.node (.leaf (.ubHGe0 5 0 3 80079706)) (.node (.leaf (.ubHGe0 5 1 2 156759090)) (.leaf (.ubHGe0 5 2 1 24981631)))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 5 3 0 972474)) (.leaf (.ubHLePi 5 0 2 65069158))) (.node (.leaf (.ubHLePi 5 1 1 58871139)) (.leaf (.ubHLePi 5 2 0 4515141))))
            (.node (.node (.leaf (.ubHGe0 5 0 1 26459954)) (.leaf (.ubHGe0 5 1 0 9433252))) (.node (.leaf (.ubHLePi 5 0 0 4389444)) (.leaf (.ubHLePi 6 0 8 1321059)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 6 1 7 272608)) (.leaf (.ubHLePi 6 2 6 565250))) (.node (.leaf (.ubHLePi 6 3 5 193015)) (.leaf (.ubHLePi 6 4 4 30550))))
            (.node (.node (.leaf (.ubHLePi 6 5 3 2205)) (.leaf (.ubHLePi 6 6 2 59))) (.node (.leaf (.ubHGe0 6 0 7 10383128)) (.leaf (.ubHGe0 6 1 6 2898724))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 6 2 5 3795483)) (.leaf (.ubHGe0 6 3 4 1038644))) (.node (.leaf (.ubHGe0 6 4 3 126952)) (.leaf (.ubHGe0 6 5 2 6594))))
            (.node (.node (.leaf (.ubHGe0 6 6 1 110)) (.leaf (.ubHLePi 6 0 6 36254290))) (.node (.leaf (.ubHLePi 6 1 5 11949488)) (.leaf (.ubHLePi 6 2 4 10580445)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 6 3 3 2231372)) (.leaf (.ubHLePi 6 4 2 197638))) (.node (.leaf (.ubHLePi 6 5 1 6578)) (.leaf (.ubHLePi 6 6 0 52))))
            (.node (.node (.leaf (.ubHGe0 6 0 5 73495713)) (.leaf (.ubHGe0 6 1 4 25857812))) (.node (.leaf (.ubHGe0 6 2 3 15677336)) (.leaf (.ubHGe0 6 3 2 2392443)))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 6 5 0 2188)) (.leaf (.ubHLePi 6 0 4 94617921))) (.node (.leaf (.ubHLePi 6 1 3 32370708)) (.leaf (.ubHLePi 6 2 2 13025414))))
            (.node (.node (.leaf (.ubHLePi 6 3 1 1280267)) (.leaf (.ubHLePi 6 4 0 35377))) (.node (.leaf (.ubHGe0 6 0 3 79169182)) (.leaf (.ubHGe0 6 1 2 23704169)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 6 2 1 5754685)) (.leaf (.ubHGe0 6 3 0 273567))) (.node (.leaf (.ubHLePi 6 0 2 41998975)) (.leaf (.ubHLePi 6 1 1 9464096))))
            (.node (.node (.leaf (.ubHLePi 6 2 0 1056395)) (.leaf (.ubHGe0 6 0 1 12895833))) (.node (.leaf (.ubHGe0 6 1 0 1596196)) (.leaf (.ubHLePi 6 0 0 1751611))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 7 0 8 5466939)) (.leaf (.ubHLePi 7 1 7 8873922))) (.node (.leaf (.ubHLePi 7 2 6 6360249)) (.leaf (.ubHLePi 7 3 5 2429262))))
            (.node (.node (.leaf (.ubHLePi 7 4 4 465937)) (.leaf (.ubHLePi 7 5 3 41083))) (.node (.leaf (.ubHLePi 7 6 2 1416)) (.leaf (.ubHLePi 7 7 1 12)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 7 0 7 50720517)) (.leaf (.ubHGe0 7 1 6 72252882))) (.node (.leaf (.ubHGe0 7 2 5 43925254)) (.leaf (.ubHGe0 7 3 4 13544328))))
            (.node
            (.node (.leaf (.ubHGe0 7 4 3 2000750)) (.leaf (.ubHGe0 7 5 2 127519)))
            (.node (.leaf (.ubHGe0 7 6 1 2835)) (.node (.leaf (.ubHGe0 7 7 0 12)) (.leaf (.ubHLePi 7 0 6 206288850))))))))))
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 7 1 5 252022961)) (.leaf (.ubHLePi 7 2 4 125912975))) (.node (.leaf (.ubHLePi 7 3 3 30090327)) (.leaf (.ubHLePi 7 4 2 3213797))))
            (.node (.node (.leaf (.ubHLePi 7 5 1 131794)) (.leaf (.ubHLePi 7 6 0 1419))) (.node (.leaf (.ubHGe0 7 0 5 480147047)) (.leaf (.ubHGe0 7 1 4 487841551)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 7 2 3 191767180)) (.leaf (.ubHGe0 7 3 2 33304818))) (.node (.leaf (.ubHGe0 7 4 1 2289086)) (.leaf (.ubHLePi 7 0 4 699132220))))
            (.node (.node (.leaf (.ubHLePi 7 1 3 565675401)) (.leaf (.ubHLePi 7 2 2 163676941))) (.node (.leaf (.ubHLePi 7 3 1 18369645)) (.leaf (.ubHLePi 7 4 0 610103))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 7 0 3 651778306)) (.leaf (.ubHGe0 7 1 2 392767099))) (.node (.leaf (.ubHGe0 7 2 1 74239463)) (.leaf (.ubHGe0 7 3 0 4040090))))
            (.node (.node (.leaf (.ubHLePi 7 0 2 379735953)) (.leaf (.ubHLePi 7 1 1 151159232))) (.node (.leaf (.ubHLePi 7 2 0 13981731)) (.leaf (.ubHGe0 7 0 1 126355643)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 7 1 0 24869983)) (.leaf (.ubHLePi 7 0 0 18377550))) (.node (.leaf (.ubHGe0 8 0 8 1968482)) (.leaf (.ubHGe0 8 1 7 3794932))))
            (.node (.node (.leaf (.ubHGe0 8 2 6 2792135)) (.leaf (.ubHGe0 8 3 5 991059))) (.node (.leaf (.ubHGe0 8 4 4 163920)) (.leaf (.ubHGe0 8 5 3 11536)))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 8 6 2 421)) (.leaf (.ubHGe0 8 7 1 31))) (.node (.leaf (.ubHGe0 8 8 0 1)) (.leaf (.ubHLePi 8 0 7 18786542))))
            (.node (.node (.leaf (.ubHLePi 8 1 6 30905072)) (.leaf (.ubHLePi 8 2 5 18964451))) (.node (.leaf (.ubHLePi 8 3 4 5393576)) (.leaf (.ubHLePi 8 4 3 685357)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 8 5 2 35460)) (.leaf (.ubHLePi 8 6 1 947))) (.node (.leaf (.ubHLePi 8 7 0 32)) (.leaf (.ubHGe0 8 0 6 78180929))))
            (.node (.node (.leaf (.ubHGe0 8 1 5 107521588)) (.leaf (.ubHGe0 8 2 4 53437201))) (.node (.leaf (.ubHGe0 8 3 3 11703641)) (.leaf (.ubHGe0 8 4 2 1074133))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 8 5 1 36553)) (.leaf (.ubHGe0 8 6 0 527))) (.node (.leaf (.ubHLePi 8 0 5 185302732)) (.leaf (.ubHLePi 8 1 4 207118047))))
            (.node (.node (.leaf (.ubHLePi 8 2 3 79976790)) (.leaf (.ubHLePi 8 3 2 12661821))) (.node (.leaf (.ubHLePi 8 4 1 748181)) (.leaf (.ubHLePi 8 5 0 12629)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 8 0 4 273589250)) (.leaf (.ubHGe0 8 1 3 238547160))) (.node (.leaf (.ubHGe0 8 2 2 67070764)) (.leaf (.ubHGe0 8 3 1 6831959))))
            (.node
            (.node (.leaf (.ubHGe0 8 4 0 195485)) (.leaf (.ubHLePi 8 0 3 257656380)))
            (.node (.leaf (.ubHLePi 8 1 2 164266992)) (.node (.leaf (.ubHLePi 8 2 1 29890642)) (.leaf (.ubHLePi 8 3 0 1471264)))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 8 0 2 151146954)) (.leaf (.ubHGe0 8 1 1 62622685))) (.node (.leaf (.ubHGe0 8 2 0 5531782)) (.leaf (.ubHLePi 8 0 1 50495754))))
            (.node (.node (.leaf (.ubHLePi 8 1 0 10196255)) (.leaf (.ubHGe0 8 0 0 7355792))) (.node (.leaf (.ubHGe0 9 0 8 641224)) (.leaf (.ubHGe0 9 1 7 670657)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 9 2 6 118347)) (.leaf (.ubHLePi 9 3 5 325129))) (.node (.leaf (.ubHLePi 9 4 4 127614)) (.leaf (.ubHLePi 9 5 3 22129))))
            (.node (.node (.leaf (.ubHLePi 9 6 2 2427)) (.leaf (.ubHLePi 9 7 1 227))) (.node (.leaf (.ubHLePi 9 8 0 13)) (.leaf (.ubHLePi 9 0 7 5556501))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 9 1 6 4245398)) (.leaf (.ubHGe0 9 2 5 1654802))) (.node (.leaf (.ubHGe0 9 3 4 2068694)) (.leaf (.ubHGe0 9 4 3 600047))))
            (.node (.node (.leaf (.ubHGe0 9 5 2 77427)) (.leaf (.ubHGe0 9 6 1 5935))) (.node (.leaf (.ubHGe0 9 7 0 281)) (.leaf (.ubHGe0 9 0 6 20687722)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 9 1 5 10529385)) (.leaf (.ubHLePi 9 2 4 7068605))) (.node (.leaf (.ubHLePi 9 3 3 5171692)) (.leaf (.ubHLePi 9 4 2 1056533))))
            (.node
            (.node (.leaf (.ubHLePi 9 5 1 90895)) (.leaf (.ubHLePi 9 6 0 3630)))
            (.node (.leaf (.ubHLePi 9 0 5 43088787)) (.node (.leaf (.ubHLePi 9 1 4 12106944)) (.leaf (.ubHGe0 9 2 3 14220515))))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 9 3 2 6378864)) (.leaf (.ubHGe0 9 4 1 826618))) (.node (.leaf (.ubHGe0 9 5 0 35781)) (.leaf (.ubHGe0 9 0 4 54646339))))
            (.node (.node (.leaf (.ubHGe0 9 1 3 4513039)) (.leaf (.ubHLePi 9 2 2 15038591))) (.node (.leaf (.ubHLePi 9 3 1 3894469)) (.leaf (.ubHLePi 9 4 0 242701)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 9 0 3 42872932)) (.leaf (.ubHGe0 9 1 2 3411376))) (.node (.leaf (.ubHGe0 9 2 1 8127509)) (.leaf (.ubHGe0 9 3 0 943856))))
            (.node (.node (.leaf (.ubHGe0 9 0 2 20044255)) (.leaf (.ubHLePi 9 1 1 3803639))) (.node (.leaf (.ubHLePi 9 2 0 1777336)) (.leaf (.ubHLePi 9 0 1 4971696))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 9 1 0 1031537)) (.leaf (.ubHGe0 9 0 0 470375))) (.node (.leaf (.ubHLePi 10 0 8 199216)) (.leaf (.ubHGe0 10 1 7 23362))))
            (.node (.node (.leaf (.ubHGe0 10 2 6 415514)) (.leaf (.ubHGe0 10 3 5 293142))) (.node (.leaf (.ubHGe0 10 4 4 88179)) (.leaf (.ubHGe0 10 5 3 22109)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 10 6 2 4512)) (.leaf (.ubHGe0 10 7 1 310))) (.node (.leaf (.ubHLePi 10 8 0 41)) (.leaf (.ubHGe0 10 0 7 1484605))))
            (.node
            (.node (.leaf (.ubHLePi 10 1 6 1017619)) (.leaf (.ubHLePi 10 2 5 3292096)))
            (.node (.leaf (.ubHLePi 10 3 4 1757110)) (.node (.leaf (.ubHLePi 10 4 3 439788)) (.leaf (.ubHLePi 10 5 2 87457)))))))))))
      (.node
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 10 6 1 10658)) (.leaf (.ubHLePi 10 7 0 100))) (.node (.leaf (.ubHLePi 10 0 6 4406248)) (.leaf (.ubHGe0 10 1 5 6320545))))
            (.node (.node (.leaf (.ubHGe0 10 2 4 10587815)) (.leaf (.ubHGe0 10 3 3 4238240))) (.node (.leaf (.ubHGe0 10 4 2 833391)) (.leaf (.ubHGe0 10 5 1 112471)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 10 6 0 5599)) (.leaf (.ubHGe0 10 0 5 6208573))) (.node (.leaf (.ubHLePi 10 1 4 17358180)) (.leaf (.ubHLePi 10 2 3 17859484))))
            (.node (.node (.leaf (.ubHLePi 10 3 2 5152096)) (.leaf (.ubHLePi 10 4 1 705483))) (.node (.leaf (.ubHLePi 10 5 0 46253)) (.leaf (.ubHLePi 10 0 4 2921855))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 10 1 3 25813445)) (.leaf (.ubHGe0 10 2 2 16771350))) (.node (.leaf (.ubHGe0 10 3 1 3156742)) (.leaf (.ubHGe0 10 4 0 222797))))
            (.node (.node (.leaf (.ubHLePi 10 0 3 3087551)) (.leaf (.ubHLePi 10 1 2 21734094))) (.node (.leaf (.ubHLePi 10 2 1 8350480)) (.leaf (.ubHLePi 10 3 0 778300)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 10 0 2 5204742)) (.leaf (.ubHGe0 10 1 1 9800730))) (.node (.leaf (.ubHGe0 10 2 0 1727111)) (.leaf (.ubHLePi 10 0 1 2863388))))
            (.node (.node (.leaf (.ubHLePi 10 1 0 1848120)) (.leaf (.ubHGe0 10 0 0 580331))) (.node (.leaf (.ubHGe0 11 0 8 139353)) (.leaf (.ubHGe0 11 1 7 1005487)))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 11 2 6 1509776)) (.leaf (.ubHGe0 11 3 5 1302477))) (.node (.leaf (.ubHGe0 11 4 4 622647)) (.leaf (.ubHGe0 11 5 3 155619))))
            (.node (.node (.leaf (.ubHGe0 11 6 2 19130)) (.leaf (.ubHGe0 11 7 1 918))) (.node (.leaf (.ubHGe0 11 8 0 28)) (.leaf (.ubHLePi 11 0 7 2075077)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 11 1 6 9728803)) (.leaf (.ubHLePi 11 2 5 12573067))) (.node (.leaf (.ubHLePi 11 3 4 8735425)) (.leaf (.ubHLePi 11 4 3 3171850))))
            (.node (.node (.leaf (.ubHLePi 11 5 2 564323)) (.leaf (.ubHLePi 11 6 1 43422))) (.node (.leaf (.ubHLePi 11 7 0 1058)) (.leaf (.ubHGe0 11 0 6 11813450))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 11 1 5 40462068)) (.leaf (.ubHGe0 11 2 4 43227037))) (.node (.leaf (.ubHGe0 11 3 3 23124219)) (.leaf (.ubHGe0 11 4 2 5990141))))
            (.node (.node (.leaf (.ubHGe0 11 5 1 674599)) (.leaf (.ubHGe0 11 6 0 24633))) (.node (.leaf (.ubHLePi 11 0 5 36100420)) (.leaf (.ubHLePi 11 1 4 93393454)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 11 2 3 78454116)) (.leaf (.ubHLePi 11 3 2 30231225))) (.node (.leaf (.ubHLePi 11 4 1 4973482)) (.leaf (.ubHLePi 11 5 0 266413))))
            (.node
            (.node (.leaf (.ubHGe0 11 0 4 66587666)) (.leaf (.ubHGe0 11 1 3 128826152)))
            (.node (.leaf (.ubHGe0 11 2 2 79248692)) (.node (.leaf (.ubHGe0 11 3 1 19534919)) (.leaf (.ubHGe0 11 4 0 1533064)))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 11 0 3 76881403)) (.leaf (.ubHLePi 11 1 2 105980885))) (.node (.leaf (.ubHLePi 11 2 1 42244914)) (.leaf (.ubHLePi 11 3 0 4995312))))
            (.node (.node (.leaf (.ubHGe0 11 0 2 54604291)) (.leaf (.ubHGe0 11 1 1 48083719))) (.node (.leaf (.ubHGe0 11 2 0 9286739)) (.leaf (.ubHLePi 11 0 1 21883258)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 11 1 0 9274320)) (.leaf (.ubHGe0 11 0 0 3795401))) (.node (.leaf (.ubHLePi 12 0 8 102414)) (.leaf (.ubHLePi 12 1 7 1609628))))
            (.node (.node (.leaf (.ubHLePi 12 2 6 2651546)) (.leaf (.ubHLePi 12 3 5 1989912))) (.node (.leaf (.ubHLePi 12 4 4 777885)) (.leaf (.ubHLePi 12 5 3 159074))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 12 6 2 15477)) (.leaf (.ubHGe0 12 7 1 247))) (.node (.leaf (.ubHGe0 12 8 0 284)) (.leaf (.ubHGe0 12 0 7 2368512))))
            (.node (.node (.leaf (.ubHGe0 12 1 6 15955323)) (.leaf (.ubHGe0 12 2 5 21056749))) (.node (.leaf (.ubHGe0 12 3 4 12567542)) (.leaf (.ubHGe0 12 4 3 3758538)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 12 5 2 548862)) (.leaf (.ubHGe0 12 6 1 29030))) (.node (.leaf (.ubHLePi 12 7 0 2024)) (.leaf (.ubHLePi 12 0 6 15776792))))
            (.node (.node (.leaf (.ubHLePi 12 1 5 66446343)) (.leaf (.ubHLePi 12 2 4 68899637))) (.node (.leaf (.ubHLePi 12 3 3 31461902)) (.leaf (.ubHLePi 12 4 2 6754215)))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 12 5 1 614925)) (.leaf (.ubHLePi 12 6 0 8456))) (.node (.leaf (.ubHGe0 12 0 5 52005698)) (.leaf (.ubHGe0 12 1 4 151227523))))
            (.node (.node (.leaf (.ubHGe0 12 2 3 119005260)) (.leaf (.ubHGe0 12 3 2 39043793))) (.node (.leaf (.ubHGe0 12 4 1 5335654)) (.leaf (.ubHGe0 12 5 0 216497)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 12 0 4 99548216)) (.leaf (.ubHLePi 12 1 3 203631530))) (.node (.leaf (.ubHLePi 12 2 2 114518766)) (.leaf (.ubHLePi 12 3 1 24014401))))
            (.node (.node (.leaf (.ubHLePi 12 4 0 1552718)) (.leaf (.ubHGe0 12 0 3 116583416))) (.node (.leaf (.ubHGe0 12 1 2 162502750)) (.leaf (.ubHGe0 12 2 1 58241339))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 12 3 0 5848257)) (.leaf (.ubHLePi 12 0 2 82742776))) (.node (.leaf (.ubHLePi 12 1 1 71252441)) (.leaf (.ubHLePi 12 2 0 12230432))))
            (.node (.node (.leaf (.ubHGe0 12 0 1 32799977)) (.leaf (.ubHGe0 12 1 0 13253579))) (.node (.leaf (.ubHLePi 12 0 0 5587317)) (.leaf (.ubHGe0 13 0 8 320332)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 13 1 7 1992986)) (.leaf (.ubHGe0 13 2 6 4112969))) (.node (.leaf (.ubHGe0 13 3 5 4504954)) (.leaf (.ubHGe0 13 4 4 2853675))))
            (.node
            (.node (.leaf (.ubHGe0 13 5 3 1034036)) (.leaf (.ubHGe0 13 6 2 208061)))
            (.node (.leaf (.ubHGe0 13 7 1 23747)) (.node (.leaf (.ubHGe0 13 8 0 2256)) (.leaf (.ubHLePi 13 0 7 4402205))))))))))
        (.node
          (.node
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 13 1 6 21400230)) (.leaf (.ubHLePi 13 2 5 36892590))) (.node (.leaf (.ubHLePi 13 3 4 32810961)) (.leaf (.ubHLePi 13 4 3 16035536))))
            (.node (.node (.leaf (.ubHLePi 13 5 2 4202565)) (.leaf (.ubHLePi 13 6 1 559886))) (.node (.leaf (.ubHLePi 13 7 0 38908)) (.leaf (.ubHGe0 13 0 6 25243783)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 13 1 5 97709054)) (.leaf (.ubHGe0 13 2 4 136830269))) (.node (.leaf (.ubHGe0 13 3 3 94554106)) (.leaf (.ubHGe0 13 4 2 33444280))))
            (.node (.node (.leaf (.ubHGe0 13 5 1 5682740)) (.leaf (.ubHGe0 13 6 0 397547))) (.node (.leaf (.ubHLePi 13 0 5 80385265)) (.leaf (.ubHLePi 13 1 4 245914623))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 13 2 3 268287113)) (.leaf (.ubHLePi 13 3 2 134810971))) (.node (.leaf (.ubHLePi 13 4 1 30761676)) (.leaf (.ubHLePi 13 5 0 2594506))))
            (.node (.node (.leaf (.ubHGe0 13 0 4 156918005)) (.leaf (.ubHGe0 13 1 3 368328693))) (.node (.leaf (.ubHGe0 13 2 2 293139695)) (.leaf (.ubHGe0 13 3 1 95188892)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 13 4 0 10588700)) (.leaf (.ubHLePi 13 0 3 193206297))) (.node (.leaf (.ubHLePi 13 1 2 328184038)) (.leaf (.ubHLePi 13 2 1 169232985))))
            (.node (.node (.leaf (.ubHLePi 13 3 0 26690541)) (.leaf (.ubHGe0 13 0 2 146898855))) (.node (.leaf (.ubHGe0 13 1 1 161031128)) (.leaf (.ubHGe0 13 2 0 40359126)))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 13 0 1 63145707)) (.leaf (.ubHLePi 13 1 0 33570670))) (.node (.leaf (.ubHGe0 13 0 0 11759389)) (.leaf (.ubHLePi 14 0 8 90620))))
            (.node (.node (.leaf (.ubHLePi 14 1 7 643278)) (.leaf (.ubHLePi 14 2 6 1693658))) (.node (.leaf (.ubHLePi 14 3 5 2245340)) (.leaf (.ubHLePi 14 4 4 1666240)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 14 5 3 712168)) (.leaf (.ubHLePi 14 6 2 170775))) (.node (.leaf (.ubHLePi 14 7 1 19044)) (.leaf (.ubHLePi 14 8 0 498))))
            (.node (.node (.leaf (.ubHGe0 14 0 7 1319899)) (.leaf (.ubHGe0 14 1 6 7618542))) (.node (.leaf (.ubHGe0 14 2 5 16321807)) (.leaf (.ubHGe0 14 3 4 17283792))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 14 4 3 9873595)) (.leaf (.ubHGe0 14 5 2 3049471))) (.node (.leaf (.ubHGe0 14 6 1 458874)) (.leaf (.ubHGe0 14 7 0 22483))))
            (.node (.node (.leaf (.ubHLePi 14 0 6 8145480)) (.leaf (.ubHLePi 14 1 5 37879414))) (.node (.leaf (.ubHLePi 14 2 4 64534324)) (.leaf (.ubHLePi 14 3 3 52522740)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 14 4 2 21681566)) (.leaf (.ubHLePi 14 5 1 4276732))) (.node (.leaf (.ubHLePi 14 6 0 298684)) (.leaf (.ubHGe0 14 0 5 27984137))))
            (.node
            (.node (.leaf (.ubHGe0 14 1 4 102762099)) (.leaf (.ubHGe0 14 2 3 134152108)))
            (.node (.leaf (.ubHGe0 14 3 2 78817527)) (.node (.leaf (.ubHGe0 14 4 1 20880405)) (.leaf (.ubHGe0 14 5 0 1958310)))))))))
          (.node
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHLePi 14 0 4 58783189)) (.leaf (.ubHLePi 14 1 3 164586099))) (.node (.leaf (.ubHLePi 14 2 2 154783539)) (.leaf (.ubHLePi 14 3 1 58406591))))
            (.node (.node (.leaf (.ubHLePi 14 4 0 7427484)) (.leaf (.ubHGe0 14 0 3 77539093))) (.node (.leaf (.ubHGe0 14 1 2 155846269)) (.leaf (.ubHGe0 14 2 1 94038707)))))
            (.node
            (.node (.node (.leaf (.ubHGe0 14 3 0 17088861)) (.leaf (.ubHLePi 14 0 2 62856372))) (.node (.leaf (.ubHLePi 14 1 1 80867163)) (.leaf (.ubHLePi 14 2 0 23508218))))
            (.node (.node (.leaf (.ubHGe0 14 0 1 28675808)) (.leaf (.ubHGe0 14 1 0 17750922))) (.node (.leaf (.ubHLePi 14 0 0 5643495)) (.leaf (.ubHGe0 15 0 8 208487))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 15 1 7 2010145)) (.leaf (.ubHGe0 15 2 6 5626985))) (.node (.leaf (.ubHGe0 15 3 5 7730225)) (.leaf (.ubHGe0 15 4 4 5903324))))
            (.node (.node (.leaf (.ubHGe0 15 5 3 2572711)) (.leaf (.ubHGe0 15 6 2 626150))) (.node (.leaf (.ubHGe0 15 7 1 78426)) (.leaf (.ubHGe0 15 8 0 843)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 15 0 7 3564961)) (.leaf (.ubHLePi 15 1 6 24415698))) (.node (.leaf (.ubHLePi 15 2 5 54897395)) (.leaf (.ubHLePi 15 3 4 60038851))))
            (.node
            (.node (.leaf (.ubHLePi 15 4 3 35184124)) (.leaf (.ubHLePi 15 5 2 11068653)))
            (.node (.leaf (.ubHLePi 15 6 1 1736228)) (.node (.leaf (.ubHLePi 15 7 0 84302)) (.leaf (.ubHGe0 15 0 6 23884982))))))))
            (.node
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 15 1 5 123695315)) (.leaf (.ubHGe0 15 2 4 219421425))) (.node (.leaf (.ubHGe0 15 3 3 183901079)) (.leaf (.ubHGe0 15 4 2 77699368))))
            (.node (.node (.leaf (.ubHGe0 15 5 1 15718896)) (.leaf (.ubHGe0 15 6 0 1128432))) (.node (.leaf (.ubHLePi 15 0 5 86111967)) (.leaf (.ubHLePi 15 1 4 340627391)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 15 2 3 460564371)) (.leaf (.ubHLePi 15 3 2 277978210))) (.node (.leaf (.ubHLePi 15 4 1 75421771)) (.leaf (.ubHLePi 15 5 0 7256177))))
            (.node (.node (.leaf (.ubHGe0 15 0 4 186646066)) (.leaf (.ubHGe0 15 1 3 552439010))) (.node (.leaf (.ubHGe0 15 2 2 536084486)) (.leaf (.ubHGe0 15 3 1 207551303))))))
            (.node
            (.node
            (.node (.node (.leaf (.ubHGe0 15 4 0 27041176)) (.leaf (.ubHLePi 15 0 3 251725396))) (.node (.leaf (.ubHLePi 15 1 2 528835794)) (.leaf (.ubHLePi 15 2 1 328428018))))
            (.node (.node (.leaf (.ubHLePi 15 3 0 61193542)) (.leaf (.ubHGe0 15 0 2 207536346))) (.node (.leaf (.ubHGe0 15 1 1 277117127)) (.leaf (.ubHGe0 15 2 0 82769872)))))
            (.node
            (.node (.node (.leaf (.ubHLePi 15 0 1 95984804)) (.leaf (.ubHLePi 15 1 0 61386175))) (.node (.leaf (.ubHGe0 15 0 0 19111651)) (.leaf (.ubPHi 8 48583939))))
            (.node
            (.node (.leaf (.ubPHi 7 525948922)) (.leaf (.ubPHi 6 1237370220)))
            (.node (.leaf (.ubPHi 5 3362440662)) (.node (.leaf (.ubPHi 4 2828921981)) (.leaf (.ubPHi 3 3136141728)))))))))))))

private lemma cert_37_8_u : checkBinoFarkasU 37 8 cert_37_8 = true := by decide
private lemma cert_37_8_c_3 : checkBinoCForJ 37 8 3 cert_37_8 = true := by decide
private lemma cert_37_8_c_5 : checkBinoCForJ 37 8 5 cert_37_8 = true := by decide
private lemma cert_37_8_c_6 : checkBinoCForJ 37 8 6 cert_37_8 = true := by decide
private lemma cert_37_8_c_7 : checkBinoCForJ 37 8 7 cert_37_8 = true := by decide
private lemma cert_37_8_c_8 : checkBinoCForJ 37 8 8 cert_37_8 = true := by decide
private lemma cert_37_8_c_9 : checkBinoCForJ 37 8 9 cert_37_8 = true := by decide
private lemma cert_37_8_c_10 : checkBinoCForJ 37 8 10 cert_37_8 = true := by decide
private lemma cert_37_8_c_11 : checkBinoCForJ 37 8 11 cert_37_8 = true := by decide
private lemma cert_37_8_c_12 : checkBinoCForJ 37 8 12 cert_37_8 = true := by decide
private lemma cert_37_8_c_13 : checkBinoCForJ 37 8 13 cert_37_8 = true := by decide
private lemma cert_37_8_c_14 : checkBinoCForJ 37 8 14 cert_37_8 = true := by decide
private lemma cert_37_8_c_15 : checkBinoCForJ 37 8 15 cert_37_8 = true := by decide
private lemma cert_37_8_c_rest :
    ([0, 1, 2, 4, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37] : List ℕ).all (fun j => checkBinoCForJ 37 8 j cert_37_8) = true := by
  decide
lemma cert_37_8_c_ok : ∀ j ≤ 37, checkBinoCForJ 37 8 j cert_37_8 = true := by
  have hcov : ∀ j : Fin 38, j.val = 3 ∨ j.val = 5 ∨ j.val = 6 ∨ j.val = 7 ∨ j.val = 8 ∨ j.val = 9 ∨ j.val = 10 ∨ j.val = 11 ∨ j.val = 12 ∨ j.val = 13 ∨ j.val = 14 ∨ j.val = 15 ∨ j.val ∈ ([0, 1, 2, 4, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37] : List ℕ) := by decide
  intro j hj
  rcases hcov ⟨j, by omega⟩ with h | h | h | h | h | h | h | h | h | h | h | h | h
  · dsimp only at h; rw [h]; exact cert_37_8_c_3
  · dsimp only at h; rw [h]; exact cert_37_8_c_5
  · dsimp only at h; rw [h]; exact cert_37_8_c_6
  · dsimp only at h; rw [h]; exact cert_37_8_c_7
  · dsimp only at h; rw [h]; exact cert_37_8_c_8
  · dsimp only at h; rw [h]; exact cert_37_8_c_9
  · dsimp only at h; rw [h]; exact cert_37_8_c_10
  · dsimp only at h; rw [h]; exact cert_37_8_c_11
  · dsimp only at h; rw [h]; exact cert_37_8_c_12
  · dsimp only at h; rw [h]; exact cert_37_8_c_13
  · dsimp only at h; rw [h]; exact cert_37_8_c_14
  · dsimp only at h; rw [h]; exact cert_37_8_c_15
  · exact List.all_eq_true.mp cert_37_8_c_rest j h

/-- **World Record `B_8 ≤ 36`**: Every Boolean function of polynomial degree `≤ 8` has
maximum sensitivity `≤ 36` (kernel-verified via `j`-sliced `by decide`). -/
theorem maxSensitivity_le_thirtysix_of_deg_le_eight_proof {m : ℕ} (f : BooleanFun m) (hf : polyDegree f ≤ 8) :
    maxSensitivity f ≤ 36 := by
  have hlt := maxSensitivity_lt_of_bino_farkas_sliced (n := 37) (d := 8) cert_37_8 cert_37_8_u cert_37_8_c_ok f hf
  omega

end DegreeSensitivity
