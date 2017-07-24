module Tests.Run where

import Prog2Proc.SeqLogic
import Tests.QR4 (qr, linFib)
import Tests.ICP (icp)

{-
testFac = simulate (interpretSeqLogic $ forever factorial) 
   [Nothing, Nothing, Just 3, Nothing, Nothing, Nothing, Nothing, Just 5, Nothing, Nothing, Nothing, Nothing, Nothing, Nothing, Nothing]
-}

testFib = simulateSeq linFib (replicate 13 Nothing)

testQR = simulateSeq qr ([Just test_a0, Just test_a1, Just test_a2, Just test_a3] ++ replicate 81 Nothing)

testICP = simulateSeq icp ([Just px, Just py, Just qx, Just qy] ++ replicate 3250 Nothing)


test_a0 = [0.00991607300528884,-0.00991607300529719,-0.512272038205321,-0.00991607300528806,-0.508784876502976,0.00991607300529443,-0.00991607300529160,-0.00991607300529526,-0.505339981737874,-0.0100038258637461,-0.506378640982157,-0.519626983777520,-0.00991607300530473,-0.0100038258637395,-0.499635397941894,-0.0100038258637523,-0.500678021121194,-0.518770110056720,-0.515498259681076,-0.512265136412032,-0.513496859628638,-0.514711251471198,-0.0205333782395740,-0.497204543840086,-0.520280823908276,-0.517089646704706,-0.535819685066999,-0.836463646259124,-0.513173313944184,-0.536724641620168,-0.850684335802459,-0.517702372345059,-0.537590105321268,-0.850806083473209,-0.873866236913789,-0.539673381521249,-0.860693491748534,-0.891161765495123,-0.891146204669361,-0.921995132181704,-0.900854216041190,-0.900676471925668,-0.900477791872703,-0.932144354509116,-1.13320334099306,-0.915421121283698,-0.947911783632615,-1.16818094223907,-1.17494224319929,-1.21520508156574,-1.34765211158310,-1.22573532432751,-1.37400651475455,-1.25072148032264,-1.40769561996909,-1.43115605030487,-1.45416303315533,-1.49641889162862,-1.69165409327159,-1.55323871816551,-1.80512490330357,-1.70513171260566,-1.82656868462436,-1.92769108168052,-1.98801524324610,-2.08537088453763,-2.07510550941437,-2.18729078848061,-2.29015820319437,-2.35433769534490,-2.48924407333662,-2.53471514600122,-2.71435351304407,-2.81828739389916,-2.91281678755042,-3.09188276472896,-3.24075206925383,-3.43142259686484,-3.59885255414456,-3.83631936772216,-4.07136040193259,-4.37153039434519,-4.69188272154083,-5.06582286211847,-5.48102866481194,-15.6734044817242,-9.93021535952791,-9.88848301068420,-7.43266278356166,-6.43400016221734,-10.5220218823999,0,-12.7647260667856,0,0,0,-5.98163795420083,0,0,0,0,0,0,0,0,0,0,0,0,-2.87330415865627,-2.98615725835192,-3.10743969956118,-3.22870444839963,-2.98946159149423,-2.84242340187235,-2.63135718314467,-2.48347326700204,-2.34981725892567,-2.15276329785448,-2.08087994202131,-2.02403645075565,-1.88844654843164,-1.86483194228401,-1.73325722728142,-1.82608818923990,-1.55761573582511,-1.52705841208013,-1.36167184427148,-1.42103458673824,-1.46477988080690,-1.16094343945491,-1.30049715894925,-1.12918520629168,-1.13212103896416,-1.09804493811270,-1.10508652408726,-0.182078449179904,1.16281975116632,1.16316544172113,1.14668603600447,-1.13713696475740,-1.13484692321133,-1.13180790311610,-1.28291790847280,-0.511355328472531,-0.486208087893654,-0.846231532192835,-0.860175473859001,-0.833314623702824,-0.682801055360968,0.0321142485511293,0.0526354981550318,-0.815184314213856,-0.498228350825383,-0.497997275901148,0.0305348592781224,-0.275190930196377,0.0297451646416202,-0.275369094252207,-0.522780922499664,-0.500961645011412,-0.270752460236264,-0.516412690924361,-0.495059746999772,-0.273531664736153,0.00938955585456547,-0.514661934253126,0.00921405013766211,-0.00912629727920328,0.00912629727921205,-0.00912629727920650,-0.00903854442074925,-0.00903854442075704,0.00903854442075043,-0.499071662212516,0.00895079156230332,0.00903854442074784,0.00895079156230624,-0.00895079156229914,0.00895079156230052]
test_a1 = [1.12995649097483,1.12995649097483,1.00721266814559,1.12995649097483,1.00897866649491,1.12995649097483,1.12995649097483,1.12995649097483,1.01070841633834,1.13995610593921,1.02136216493322,1.00343798898102,1.12995649097483,1.13995610593921,1.02467773915678,1.13995610593921,1.03528813340353,1.02634184018374,1.02798907789226,1.02960401612307,1.04015430352978,1.05070087446854,1.16981980679850,1.07013440351424,1.07023729344166,1.07178276589559,1.06254282976956,0.860423482063856,1.09578882539271,1.09559420365284,0.902184105834463,1.13775403917907,1.12849318946136,0.929370221346143,0.921551843350190,1.17168794534954,0.974272401980943,0.973771383703391,0.987298557632590,0.986116106872432,1.03216359238292,1.04555339075512,1.05888608752031,1.05792575465237,0.872209944888362,1.12450174331021,1.12354939831341,0.940932136867184,0.964318788132757,0.962172858553396,0.805440119528202,1.01275511092056,0.858199334311125,1.07619504675479,0.916947676544214,0.954040019955009,0.991468543628330,0.982257858597716,0.723813808045605,1.07682379449544,0.682952475266959,0.986623455359996,0.885746487630419,0.807531481497401,0.792082945543683,0.731661310937467,0.895286057524706,0.831480009758421,0.782032866535376,0.840888825159463,0.715376784190344,0.870413194196888,0.687229951490258,0.683561383775489,0.834504860479841,0.699400435495985,0.673517650568259,0.579429859193827,0.666228409426680,0.509464138914471,0.562249479835489,0.402271066963826,0.412718460099152,0.379260767332705,0.313727231062020,-7.69389089032786,-1.73124894610683,-1.90336642489299,-6.61498480314637,-7.68140884946162,-2.60627233924206,0,-3.40086289637254,0,0,0,5.96845938118574,0,0,0,0,0,0,0,0,0,0,0,0,6.20723152555538,6.16484913265460,6.13825858966459,6.10930172645650,-1.42099239722835,-1.35761894671826,-1.41988005645299,-1.37766488381109,-1.34998475904547,-1.45794724987248,-1.36749357106109,-1.28968075352487,-1.31292407766658,-1.25892884113330,-1.30564902790785,-1.03701587505619,-1.30181919616743,-1.24458531491228,-1.33938410790867,-1.18455084453715,-1.04614525797488,-1.32280396521428,-1.09485484862831,-1.23038236735253,-1.14472789480064,-1.14995535299640,-1.07255945023142,-1.50905514754904,-0.931638463298661,-0.898858250885911,-0.854406890674668,0.816651408731004,0.785189442668308,0.754062908810629,-0.350744408536714,-1.21692880976775,-1.21642989739105,-0.999996096953667,-1.05342211585453,-0.918252001317188,-1.02307512861859,-1.21957725259206,-1.19884507103044,-0.866933984718378,-1.06965812783049,-1.05872504135636,-1.15959804344819,-1.10628655959369,-1.12960843887625,-1.09593424160883,-0.979183387864807,-0.979304564590332,-1.05583763206092,-0.948534623855271,-0.948586235879755,-1.04478726465567,-1.06995880118856,-0.926673131924538,-1.04995957125980,-1.03995995629542,-1.03995995629542,-1.03995995629542,-1.02996034133104,-1.02996034133104,-1.02996034133104,-0.889565891868858,-1.01996072636666,-1.02996034133104,-1.01996072636666,-1.01996072636666,-1.01996072636666]
test_a2 = [0.00877528584538835,0.00877528584538835,-0.421777849160758,0.0438629151291984,-0.386509975159139,0.0963795441629286,0.0963795441629286,0.113832895747467,-0.317630918970467,0.148629044388467,-0.280930964244145,-0.280930964244145,0.200466599321711,0.217629367674856,-0.206473413537934,0.251748534240115,-0.168826459335890,-0.168826459335890,-0.148353165314574,-0.127858426560832,-0.107350597826155,-0.0868379593079803,0.360278789681376,-0.0312707556307566,-0.0312707556307566,-0.0107452567467093,-0.0107452567467093,-0.293042705437321,0.0534177854249439,0.0534177854249439,-0.227493020139200,0.116785766655356,0.116785766655356,-0.161408497397809,-0.161408497397809,0.181634492721118,-0.0916226475764997,-0.0916226475764997,-0.0672744522167938,-0.0672744522167938,-0.0155401284469720,0.00848714562315547,0.0324009782737619,0.0324009782737619,-0.142097545332399,0.106324061756417,0.106324061756417,-0.0677907523905329,-0.0410882188107773,-0.0410882188107773,-0.153943436765545,0.0148329144451870,-0.0996801357404216,0.0698739553649557,-0.0456911983804483,-0.0175299597709860,0.0104640699203314,0.0104640699203314,-0.148002448565732,0.0708405419531392,-0.155419504981360,0.0243504932423710,-0.0311278791713374,-0.0683406708246191,-0.0683406708246191,-0.0924267486461868,-0.00512995982248330,-0.0316170082611969,-0.0482628799507457,-0.0167462974350379,-0.0623544690483980,0.00609043011043828,-0.0591316375227113,-0.0516152691142694,0.00698307290863287,-0.0320196626936511,-0.0320196626936511,-0.0520794668017115,-0.0187828968272809,-0.0522318735021949,-0.0294976096594090,-0.0573880032617225,-0.0438783590377418,-0.0393428636610485,-0.0393428636610485,-0.510107957685533,-0.231903896566760,-0.231903896566760,-0.684255653034641,-0.772212902037101,-0.231903896566760,0,-0.214813903938223,0,0,0,0.782316098191253,0,0,0,0,0,0,0,0,0,0,0,0,0.995836325747084,0.995836325747084,0.995836325747084,0.995836325747084,-0.0312718952227793,-0.0155946167556442,-0.0472605029653594,-0.0413619012362955,-0.0388064900657770,-0.0949490971290850,-0.0636082291922950,-0.0320071171199989,-0.0546470235660440,-0.0234082498184782,-0.0576211134201214,0.0889109812422674,-0.0730601834761485,-0.0432159146855690,-0.118711370778550,-0.0191789808431643,0.0729990039398717,-0.139213105285366,0.0285965830541989,-0.0822579893778162,-0.0274719579664836,-0.0274719579664836,0.0280950948997799,-0.592861453856130,-0.998099136744049,-0.998099136744049,-0.998099136744049,0.998099136744049,0.998099136744049,0.998099136744049,0.622625492397651,-0.214791768126356,-0.214791768126356,0.122816950647802,0.122816950647802,0.191675661499583,0.0619470106481172,-0.510098500921551,-0.510098500921551,0.277097271917053,-0.0204181959066467,0.000897670959616509,-0.432753918352743,-0.159184587811411,-0.400849329621953,-0.122093157534936,0.138927585483388,0.138927585483388,-0.0648440353994292,0.198860273824231,0.198860273824231,-0.00720285315160373,-0.251748534240117,0.275210936712095,-0.217629367674850,-0.183242082732142,-0.183242082732142,-0.148629044388468,-0.131251184231295,-0.113832895747466,-0.113832895747466,0.410969097531101,-0.0788965055038212,-0.0613891649405758,-0.0438629151292005,-0.00877528584539279,-0.00877528584539279]
test_a3 = [0.999961496437904,0.999961496437904,0.906699203681863,0.999037559192030,0.922285226544632,0.995344655617815,0.995344655617815,0.993499910340080,0.948214426864502,0.988893021091853,0.959727978819444,0.959727978819444,0.979700537182862,0.976031484290052,0.978452211148809,0.967792682090515,0.985645791665600,0.985645791665600,0.988934445927103,0.991792429270051,0.994221227467191,0.996222449467600,0.932844678231978,0.999510950336354,0.999510950336354,0.999942268062235,0.999942268062235,0.956099352991087,0.998572250866353,0.998572250866353,0.973779711119484,0.993157129917880,0.993157129917880,0.986887682042785,0.986887682042785,0.983366112418942,0.995793799162795,0.995793799162795,0.997734507812038,0.997734507812038,0.999879244913030,0.999963983530993,0.999474950464945,0.999474950464945,0.989852659546110,0.994331531176407,0.994331531176407,0.997699560935217,0.999155522566411,0.999155522566411,0.988079661908296,0.999889986273021,0.995019532742333,0.997555828192917,0.998955611821946,0.999846338449278,0.999945250121577,0.999945250121577,0.988986994463804,0.997487652863826,0.987848559988498,0.999703482778195,0.999515410155489,0.997662043334937,0.997662043334937,0.995719486670164,0.999986841669539,0.999500057423016,0.998834668210340,0.999859770929013,0.998054066766772,0.999981453158542,0.998250193811092,0.998667043610763,0.999975618049137,0.999487239138642,0.999487239138642,0.998642943768016,0.999823585832409,0.998634984060968,0.999564850834793,0.998351950507251,0.999036881004978,0.999225769823291,0.999225769823291,0.860110383326405,0.972738702199698,0.972738702199698,0.729242210304736,0.635363859475370,0.972738702199698,0,0.976654998796822,0,0,0,0.622881628008736,0,0,0,0,0,0,0,0,0,0,0,0,0.0911592689886656,0.0911592689886656,0.0911592689886656,0.0911592689886656,0.999510914682364,0.999878396570425,0.998882598136268,0.999144230392249,0.999246744467439,0.995482128897537,0.997974946167999,0.999487640970946,0.998505734993732,0.999725989379308,0.998338523391853,0.996039576229046,0.997327533757307,0.999065755952975,0.992928804319765,0.999816066431130,0.997332013636275,0.990262445676299,0.999591034092255,0.996611069165660,0.999622574537754,0.999622574537754,0.999605254909443,0.805304474426658,-0.0616288344103960,-0.0616288344103960,-0.0616288344103960,0.0616288344103960,0.0616288344103960,0.0616288344103960,0.782519965378892,0.976659867274761,0.976659867274761,0.992429340877010,0.992429340877010,0.981458323510834,0.998079439659871,0.860115991804353,0.860115991804353,0.960841871431573,0.999791526907444,0.999999597093343,0.901512088743322,0.987248837428189,0.916143992471506,0.992518645106050,0.990302542656413,0.990302542656413,0.997895410888896,0.980027852407549,0.980027852407549,0.999974059116774,0.967792682090515,0.961383867304862,0.976031484290054,0.983067820201631,0.983067820201631,0.988893021091853,0.991349144669971,0.993499910340080,0.993499910340080,0.911649275146135,0.996882812280002,0.998113906539679,0.999037559192030,0.999961496437904,0.999961496437904]


px = [1.13000000000000,1.12982596724983,1.12930392260533,1.12843402686804,1.12721654798547,1.12565186096859,1.12374044777632,1.12148289716705,1.11887990451731,1.12580777843597,1.12248728607776,1.10900682263530,1.10503113976730,1.11045592380830,1.10575962573036,1.10072272873437,1.10495508942371,1.09919163647759,1.09308960770234,1.08665088266052,1.08926768327365,1.09142827353141,1.08386244060211,1.08515901643307,1.08598346875708,1.07727715081456,1.06823900719902,1.06776990439933,1.06681173187652,1.06535932823940,1.07205332669288,1.06950826764995,1.05798818458104,1.05451135501421,1.05051759879306,1.05417491889881,1.04903343305393,1.05132610606762,1.04501321322729,1.04590878599996,1.04603834360783,1.03787156123724,1.02915375850190,1.02716790224831,1.02438474674790,1.02079624840368,1.01639476255472,1.01795944482489,1.01178072665599,1.01129093757848,1.00330119861225,0.994462466758101,0.990886256524993,0.986171784272531,0.980309327062233,0.978981528673939,0.976197797191607,0.966545448187271,0.966211390500863,0.964086166741733,0.955205238134013,0.944810106268888,0.942174473190837,0.937383209552668,0.926093385274873,0.921273475522310,0.905919484945613,0.900219908428663,0.891651169204429,0.880197347409474,0.869200201256484,0.854959545334783,0.846531600309757,0.828116888539008,0.814144101626383,0.798042853541180,0.776940085208873,0.757350199508475,0.733707753517499,0.709146860173372,0.682100217362682,0.652481504865370,0.618193077729380,0.578271110397144,0.529123697454472,1.37753290720016,0.618802782601061,0.441699555350986,0.261915387773563,0.0879283641708306,-0.0951240985640509,0,-0.579429108856654,0,0,0,-0.961887969066114,0,0,0,0,0,0,0,0,0,0,0,0,-2.29549396779705,-2.41174073190196,-2.53494216699441,-2.65834169540259,-1.32681128104866,-1.31312735198881,-1.29393421587471,-1.27376474408114,-1.25777971544196,-1.24695750065945,-1.23236323469103,-1.22423640221172,-1.20776423812608,-1.21493142928568,-1.20360751131011,-1.19526814547400,-1.18454043686686,-1.17742934243448,-1.16826712960663,-1.15707897075628,-1.15028162898220,-1.14830454847621,-1.13159686533894,-1.13332818190505,-1.11319426375041,-1.11935588618059,-1.10318357342081,-1.10730156838115,-1.10319359724305,-1.10555883697011,-1.09185024186803,-1.08464614844441,-1.08429942425088,-1.08318447291816,-1.07324189689363,-1.07869061468715,-1.08360476725898,-1.09635704370525,-1.15109114482417,-1.06095220150875,-1.06340773534859,-1.06535932823940,-1.05799510599324,-1.05887182186267,-1.05926220881920,-1.05917165248154,-1.05860573425060,-1.04837396502856,-1.04680731442768,-1.05411448640213,-1.04231649002909,-1.03940519211006,-1.03605884556135,-1.03228431947461,-1.02808864842033,-1.04278995353783,-1.03786210485218,-1.03252919231298,-1.02679884668643,-1.02067884561125,-1.02402348905340,-1.02705271015212,-1.01986398376357,-1.02223662308147,-1.02429439045098,-1.01607513113979,-1.01748750349131,-1.02857260856113,-1.01937168235172,-1.01984290849100,-1.02000000000000]
py = [0,0.0198313824023206,0.0396566562913330,0.0594697150352888,0.0792644557649801,0.0990347812535607,0.118774601794630,0.138477837077998,0.158138418062563,0.179323300251420,0.199053491789967,0.216803753077199,0.236233317177259,0.257851975519006,0.277300649304429,0.296663908232113,0.318707154542584,0.338049916872804,0.357288552199964,0.376417134590233,0.398868291765162,0.421526183927213,0.440615716755574,0.463497474700798,0.486559251876206,0.505543213121157,0.524371455648039,0.547601525983121,0.570975243535668,0.594482549561627,0.623138559813723,0.647033280000653,0.665703388369714,0.689641792633026,0.713661526653966,0.743515460743547,0.767807825132755,0.798193847821876,0.822707350265188,0.853565938500408,0.884705478508067,0.909517796623554,0.934313941542886,0.965932761940921,0.997765448705377,1.02979367799816,1.06199891085224,1.10170711565815,1.13432788961899,1.17464489935114,1.20759542267401,1.24062258653041,1.28161789415952,1.32286250680285,1.36432900111183,1.41421185347714,1.46445821407040,1.50661537778840,1.56589768148062,1.62561922451023,1.67704590069603,1.72865087946993,1.79811213834610,1.86799698031039,1.92923586991071,2.00881935058856,2.07048542298560,2.15990835834965,2.24974625068170,2.33992577438117,2.43979323102096,2.53996932576772,2.66896688808179,2.77924853493107,2.91857317567797,3.06790280222693,3.21752453044194,3.39658956532939,3.58570396608927,3.80447246418032,4.05300373716504,4.34124036259323,4.66925447139557,5.04697954452760,5.46444215934180,17.4055729055260,10.0609881779200,10.0603082210637,9.94655218302540,10.0196141943078,10.8395826213869,0,13.1972861569267,0,0,0,8.39507424237367,0,0,0,0,0,0,0,0,0,0,0,0,6.44331494215574,6.41139662180441,6.39597281185542,6.37819092145132,3.03243661508069,2.86324930061265,2.69552114534253,2.53833082491938,2.40043541621572,2.28146816579788,2.16364989260783,2.06427838033045,1.95737210185078,1.89379027934295,1.80561041166634,1.72665400715232,1.64856420967679,1.57941765963735,1.51104331965721,1.44349168873035,1.38450430625046,1.33379033732774,1.26865619233703,1.22656725543274,1.16314166426674,1.12922203311522,1.07451663706733,1.04128921854624,1.00153077186971,0.968834174664221,0.923451703844186,0.885179491778201,0.853636198019518,0.822381540180114,0.785526467251204,0.760806517970141,0.736139055052516,0.717008530435924,0.724285286546249,0.641857013760648,0.618113248847483,0.594482549561627,0.566256439870085,0.543038179933262,0.519964972827468,0.497046688530886,0.474293052249074,0.447785695897381,0.425551931567350,0.407115032339958,0.381675692982181,0.360051172216745,0.338647410346053,0.317472965410981,0.296536222052665,0.281050018325160,0.260273416452403,0.239757100043988,0.219508834545241,0.199536197522378,0.181592659176813,0.163593186194278,0.144143867791540,0.126223161230388,0.108263575087141,0.0893942273262229,0.0715484467967078,0.0542069083949980,0.0357962738204956,0.0179008938498823,0]
qx = [1.14000000000000,1.13982442713700,1.14929160265144,1.14840631052942,1.15714265102933,1.15553642364918,1.15357426497392,1.15125677939272,1.15848627281881,1.15543429892113,1.16187280488751,1.16789214065133,1.16370535957796,1.15916013099288,1.16395750076880,1.15865550393092,1.16260492017626,1.16609895348058,1.16913062389033,1.17169312565134,1.17377983111385,1.17538429457229,1.15797269295098,1.15872911924209,1.15899076077437,1.16780464247965,1.16698378937709,1.16564881230260,1.17261124247585,1.17014877036131,1.16715483148016,1.17218106134435,1.17648286125411,1.17167928334912,1.17459448054027,1.17675339784053,1.18621472814559,1.18672416518239,1.18644357291219,1.18536329079996,1.19110935476512,1.18828772953250,1.18463741985831,1.18743523451400,1.18914592979127,1.19679560157673,1.19616526477528,1.20119214489337,1.19816138682946,1.20050020977058,1.20140525693696,1.20086033721733,1.21108320241944,1.20731333589728,1.21955148426194,1.21803515776874,1.22024724648951,1.22573081976821,1.23401998243317,1.23443837223016,1.23731248462955,1.24216151027230,1.24385595475441,1.25133930844591,1.25065882403943,1.25893479460515,1.26668388160537,1.26569380287620,1.27115559246086,1.28156733782819,1.28534238255303,1.29839005578827,1.30607732619220,1.32498702166241,1.34078517066523,1.35692459955425,4.10768927225235,2.25899283646494,2.02070332116295,1.83425324814869,1.65629201199016,2.03027274634646,1.42276283706719,1.05409261462157,0,0,0,0.368887116236523,0.224273276766910,0,0,0,0,0,0,0,0,0,0,0,0,-1.37319620535379,-1.49511375592621,-1.62195044978650,-0.853427531074007,-0.862509097762604,-0.868094945227098,-0.870718217461464,-0.877290578235318,-0.882624142588631,-0.887238926188750,-0.891651169204429,-0.900219908428663,-0.905919484945613,-0.908767500741463,-0.913110767724291,-0.914957773917437,-0.918968205378255,-0.911238173558826,-0.915611238625867,-0.918177301658793,-0.924202199609520,-0.917948191015843,-0.926278591653400,-0.922063997937082,-0.927792755969613,-0.926403797346923,-0.929720438220981,-0.931917657528031,-0.933006210174449,-0.932997445636917,-0.931903300867359,-0.936522689238902,-0.940338011615250,-0.936316558880619,-0.938422390377446,-0.954319114854809,-0.984729855257218,-1.02282994440772,-0.946779230710737,-0.945191643644412,-0.950726306770696,-0.955751005516020,-0.952199577695103,-0.956112135745432,-0.959527885511769,-0.954081702155714,-0.956421318861259,-0.958279407814355,-0.968306230561315,-0.960569886117493,-0.961012221277197,-0.960992913959398,-0.960517426641139,-0.968644160816453,-0.967346619228999,-0.974803862219535,-0.972697062078821,-0.979486912143576,-0.976584819486720,-0.973261225339419,-0.979028083420356,-0.974935190614909,-0.970438817667784,-0.975201715808525,-0.979664229813739,-0.974084143691492,-0.977903663510889,-0.981421966933893,-0.984637970243652,-0.987550682838572,-0.990159207537445,-0.992462740855796,-0.994460573253382,-0.986190568459211,-0.987561400447448,-0.988628041238372,-0.989390162282548,-0.989847528829497,-0.990000000000000]
qy = [0,0.0200068813616332,0.0403585440133035,0.0605222763633470,0.0813688218472362,0.101664023233744,0.121927909806876,0.142154239832281,0.163736238170972,0.184042334468563,0.206037824835229,0.228315456780413,0.248776679151273,0.269161272690892,0.291895420320451,0.312277798139066,0.335335353910023,0.358626868334627,0.382143408005179,0.405875866862512,0.429814969574528,0.453951274998537,0.470743287132024,0.494921032307632,0.519269117548556,0.548025836072515,0.572842766674329,0.597798332531574,0.627600887522677,0.652956242961132,0.678416980442360,0.709148474880715,0.740262167867122,0.766268658481140,0.797952258148529,0.829970746876517,0.868213463803961,0.900991540344390,0.934051202180777,0.967374730300462,1.00740185873911,1.04133197004726,1.07546928522922,1.11664567515156,1.15824520618946,1.20734431213577,1.24983545290773,1.30001439647661,1.34328302718039,1.39441717084264,1.44603783097270,1.49811029316879,1.56642187063941,1.61950440226774,1.69729024543078,1.75954265490760,1.83057276758800,1.91062397071489,1.99992366928232,2.08148070016653,2.17233924960625,2.27269328823712,2.37386233042736,2.49364190194545,2.60536993646820,2.74508345646039,2.89501501620996,3.03679423032921,3.20728287803796,3.40693192749899,3.60787956556381,3.85734147607262,4.11783462732619,4.44679765588970,4.80649509789870,5.21640255646787,17.0110813543003,10.1312068069308,9.87538141480323,9.84050888021834,9.84160031554917,13.5082786681147,10.7462247282225,9.19980916974913,0,0,0,8.40190587280497,8.51704769842979,0,0,0,0,0,0,0,0,0,0,0,0,6.71094867970259,6.70533629707267,6.71694698046943,3.28081719228684,3.09195376037171,2.91341915385877,2.74522308488413,2.60631180815718,2.47747343536105,2.35864518057622,2.24974625068170,2.15990835834965,2.07048542298560,1.98155030963034,1.90219050724841,1.82330805733646,1.75382366203215,1.66722673654461,1.60753104470863,1.54820878524784,1.49781517359016,1.43086376661468,1.38957114630543,1.33199023408893,1.29123994748084,1.24268902154208,1.20250567847066,1.16259600876120,1.12298682618093,1.08370464907879,1.04477568780697,1.01357054640550,0.982529604597988,0.944569373612101,0.914036879583248,0.897426892299721,0.893983843346791,0.896336379281184,0.800755323613141,0.771370699978146,0.748478115654795,0.725630770747160,0.696933256658963,0.674351231837170,0.651848323557953,0.623961621906071,0.601795863086221,0.579741818880585,0.562834828218847,0.536008856162123,0.514349599548660,0.492841373384809,0.471493661801178,0.454564065579528,0.433405720158637,0.416362138290548,0.395424361190900,0.378292729165448,0.357606054686007,0.337138824893861,0.320006268492142,0.299835578443704,0.279908022685226,0.262833813433714,0.245678645436380,0.226185943437724,0.209056032900229,0.191861728386902,0.174608326131551,0.157301140571421,0.139945502710233,0.122546758476105,0.105110267074894,0.0867649853460399,0.0694440807144517,0.0521017857388815,0.0347434422375398,0.0173743969719446,0]


