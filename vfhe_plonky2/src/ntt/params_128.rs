pub const N: usize = 128;
pub const LOGN: u32 = 7;
pub const NINV: u64 = 18302628881372282881;

pub const ROOTS: [u64; 128] = [1, 281474976710656, 18446744069397807105, 18446742969902956801, 17293822564807737345, 4096, 4503599626321920, 18446744000695107585, 70368744161280, 18446744068340842497, 64, 18014398509481984, 4398046511104, 288230376084602880, 18446744052234715141, 262144, 549755813888, 36028797010575360, 9223372032559808513, 32768, 8, 2251799813685248, 18446744069280366593, 18446735273321564161, 18446744069412487169, 18446743931975630881, 35184372088832, 2305843008676823040, 562949953290240, 18446744060824649729, 512, 144115188075855872, 17870292113338400769, 576469548262227968, 18446744035054321673, 18446744035055370249, 18410715272395620481, 36028797018964096, 140735340838912, 18446603329778778113, 2198989700608, 18446741870357774849, 562949953421314, 562949953421310, 9007336691597312, 9007061813690368, 16140901060200898561, 2305843009213702144, 1125917086449664, 1125882726711296, 18158513693262873601, 288230376151712768, 13835128420805115905, 4611756386097823744, 18446743794532483137, 18446743794540871745, 18446744065119551490, 18446744065119682562, 72058693532778496, 72056494509522944, 17591917604864, 18446726476960108545, 4503599627370512, 4503599627370480, 13797081185216407910, 13664737158269917819, 14004640413449681173, 17534372342291866343, 15104850399680027611, 10467450029535024137, 10832292272906805046, 12079821679951430619, 3051558327610197629, 10853271128879547664, 16016224591364643153, 7546206866789277329, 1654663398520981866, 10737174897695903067, 7479733969963382412, 5834015391316509212, 14041890976876060974, 12871361905596103084, 10158338780952714962, 9952623958621855812, 18142929134658341675, 17084176919086420947, 1356658891109943458, 11147770252432840497, 8668109077711679267, 4497639551463306333, 13237307188167854928, 12110422903908887252, 5965722551466996711, 13039192753378044028, 17449332314429639298, 5029422726070465669, 281721071064741919, 6336932523019185545, 3291437157293746400, 8180754653145198927, 16940035449150731648, 10231374777478672322, 9362914843564906265, 15603425602538700070, 11387280211730213981, 7737793303239342069, 18030148548143482816, 18182056015521604139, 15951685255325333175, 8930739766887302688, 14251112719600934854, 9171943329124577373, 4299803665592489687, 1116342470860912836, 6393075107303762937, 8064021942171041292, 2253768568517935352, 13801972045324315718, 7884753188935386879, 10105805016917838453, 411429644661718300, 3328437340319972906, 16933017626115159474, 16105685926854668541, 17311265416183374564, 6562114217670983589, 15113979899245772281, 16329239638270742865];

pub const INVROOTS: [u64; 128] = [1, 18446462594437873665, 1099511627520, 16777216, 68719476736, 18442240469788262401, 18446744069414580225, 1152921504606846976, 18446744069414322177, 17179869180, 18158513693329981441, 18446739671368073217, 18428729670905102337, 18446744069414584257, 1073741824, 18446673700670423041, 18302628881338728449, 18446744069414583809, 8589934592, 18446181119461294081, 16140901060737761281, 18446708885042495489, 137438953440, 2097152, 8796093020160, 134217728, 18444492269600899073, 18446744069414584313, 18446744069414551553, 9223372036854775808, 18410715272404008961, 18446743519658770433, 18442240469787213841, 18442240469787213809, 17592454475776, 18446726477496979457, 18374687574905061377, 18374685375881805825, 4294901759, 4295032831, 274873712576, 274882101184, 13834987683316760577, 4611615648609468416, 18158513693262871553, 288230376151710720, 18445618186687873025, 18445618152328134657, 16140901060200882177, 2305843009213685760, 18437737007600893953, 18437736732722987009, 18446181119461163011, 18446181119461163007, 2199056809472, 18446741870424883713, 140739635806208, 18446603334073745409, 18410715272395620225, 36028797018963840, 34359214072, 34360262648, 17870274521152356353, 576451956076183552, 2117504431143841456, 3332764170168812040, 11884629851743600732, 1135478653231209757, 2341058142559915780, 1513726443299424847, 15118306729094611415, 18035314424752866021, 8340939052496745868, 10561990880479197442, 4644772024090268603, 16192975500896648969, 10382722127243543029, 12053668962110821384, 17330401598553671485, 14146940403822094634, 9274800740290006948, 4195631349813649467, 9516004302527281633, 2495058814089251146, 264688053892980182, 416595521271101505, 10708950766175242252, 7059463857684370340, 2843318466875884251, 9083829225849678056, 8215369291935911999, 1506708620263852673, 10265989416269385394, 15155306912120837921, 12109811546395398776, 18165022998349842402, 13417321343344118652, 997411754984945023, 5407551316036540293, 12481021517947587610, 6336321165505697069, 5209436881246729393, 13949104517951277988, 9778634991702905054, 7298973816981743824, 17090085178304640863, 1362567150328163374, 303814934756242646, 8494120110792728509, 8288405288461869359, 5575382163818481237, 4404853092538523347, 12612728678098075109, 10967010099451201909, 7709569171718681254, 16792080670893602455, 10900537202625306992, 2430519478049941168, 7593472940535036657, 15395185741804386692, 6366922389463153702, 7614451796507779275, 7979294039879560184, 3341893669734556710, 912371727122717978, 4442103655964903148, 4782006911144666502, 4649662884198176411];

// Test Vectors

pub const TESTG: [u64; 128] = [10722678314349441830, 13186546025501293537, 3574496377155965819, 16687584424555541471, 176844238231484429, 3947453502504645211, 12766457768741056703, 8990653537026553958, 194770739367632940, 7814999737944573484, 11462960926279336421, 14837712838731621413, 15172203591734882590, 11241936437512707303, 11560367256303536349, 5342501531252971356, 6674631494443839592, 2729222615449852594, 15403045141574996616, 16700504079259098699, 9031268677307702756, 18089841274654193886, 5200925752062707503, 1398938149044820838, 3531556754369651570, 8758092474378820913, 4957838344942384025, 12300534948856138091, 17163907170237492810, 17764455148439249700, 7769190395827200854, 2765098470161428081, 3257917831570877686, 10220340665271028987, 697055131929320488, 612971624634182012, 6813366989387379912, 7241050003458368628, 1694326315850375693, 4277771234223232221, 12579871233870372069, 18230854723105356576, 14953190409642353114, 4046909673012920077, 16437616948596909827, 6477374075385332847, 10723395230290790906, 1246630978642159160, 15469758884205141698, 7234009268476371473, 9888154167606618952, 8126043786048063716, 2126824627158721804, 13015957560381036491, 577964078503127859, 869906256839727670, 549183266588570154, 6330438416643651943, 7122070745656990032, 11830953533020604082, 15200772847582019161, 3033176794547581134, 9636319852726725770, 11351214800849266203, 13459884419952294868, 12429474685346130046, 1441263926497216813, 10119210587849229870, 8120952766954307275, 7045567038485643500, 12526673304355155277, 16212235037709190611, 1563727613881729313, 16060063363292099992, 6584511019085328602, 2090351353491644738, 7542531302242804423, 11692796985033255965, 2699179284800015851, 4186525375933337685, 3770207481432592682, 16606819162513581456, 5038077222961123632, 2266733883447615794, 7411986302136554760, 15076106358374884702, 12556012017857629330, 10466495686301095215, 542297282767216443, 9215727070010274605, 8011752909717831773, 9412387783156960442, 2065574548879696803, 11439770524075001208, 617677595763530064, 10974997004873502288, 13153810697284115649, 3826337391115632835, 5873343480604430685, 4533915778675515164, 9728622942985157097, 10665498364693689555, 2061714962582213188, 12544918155024497197, 14108338823666055062, 12802009818981991540, 1246121093760648227, 2386245714092768225, 16025876121917272431, 5503050879080036376, 15806215683061913749, 5218381968581981907, 17256096326110462403, 14833454281551506119, 16464932023329992269, 16733322316937385394, 7421885000621416895, 16618020249058667625, 8516778590869894604, 2692751019693043871, 12410891164125439289, 304715060564248284, 12783775707610642258, 18177386879863653979, 11013852043022069658, 2590076070544767568, 6390616895705792760, 7251126552482411004];

pub const TESTGHAT: [u64; 128] = [9997468253758388568, 5456885986443302095, 5113782384404253991, 15009809240907764601, 3525105197955814488, 449132349938019106, 15245294147475238417, 5975919350835457053, 7677328373833055361, 3123603476390221129, 4380484625598970190, 12634987008441467126, 18242232754020169312, 4327757999669366506, 8937383448907274234, 11384219651699992654, 4318828418947118211, 7470452647475687971, 8604028517855183181, 10745020759713114453, 2032806992507119992, 8660121709501839030, 11656494275137034918, 14631191335754188703, 10721565572673558265, 15216407303657170799, 18229460157123460359, 1278696885952554599, 2424636066663664316, 8560513596113869021, 1031535826476143378, 5725966231565153777, 5818394768018872649, 5507936838568712895, 17634324539506824601, 317874886509627272, 8760455787527957589, 17700030298223655703, 5818469896487544476, 14745086491413983247, 7492087303331913349, 12793936579260450254, 8747550371728930972, 16295320064445657284, 18409545225066583917, 10588328057576189256, 8524289489060980114, 2297595296188162670, 4937834249860014396, 16765979419127471334, 13045555782306313831, 1301815965997337021, 10843622593522201950, 3687387551152649197, 15416849452636475163, 10257753826442757119, 5062242315938791561, 17421916922313232312, 18033887790554963776, 8325934622939529748, 14118760191403335261, 15746021134232005724, 3688701804235550312, 17554297355488151264, 6023453049466199372, 1850282582255800678, 11804665357273871595, 15909199080599256705, 12805939863635083318, 18110777365579193515, 16621057663833515593, 7003266231277591008, 4433346304521440216, 4614895135667991818, 1492995412965040145, 1633240822543535581, 12770344763133306431, 3802823238935663122, 108486052794049236, 2186056866578448208, 6402452093719554878, 12501258454374905518, 1677955814419297385, 15090053606864682795, 9247730678172942635, 16910704945540986944, 7863478103140822091, 18429451941232860608, 15586845104217422714, 17452773853837202747, 1340695697775649943, 8484980062564099369, 12159379899005862568, 12235791964809494615, 5312530334943082457, 8955219805683816227, 15827140002246665721, 1442186078960197143, 17217214670415972504, 17188806244935937006, 3082851585820882232, 6572653239170464958, 799032771833967225, 11384673902094865984, 14170678003804196561, 9637259152351841866, 10866467220305659751, 17350941229114308058, 11627914339147286052, 7324570862958795663, 17404024177003879333, 16682268048596549078, 5279741794381882759, 5201931046061492585, 10903305305546812687, 360757619384531631, 13050227720844648064, 12127108887644561782, 8120912547268895003, 3569734724606217302, 3354703580777775208, 17525304741069597981, 11349332571320962874, 3084485628162084135, 4561258195723946267, 8122547673097918799, 10429227478767082403, 1145082929337720359];
