sig Username {}

sig Password {}

sig FiscalCode {}

sig Registration {
	username: one Username,
	password: one Password
}

abstract sig User {
	registration: one Registration
}

sig Citizen extends User {
	reports: set Report,
	fiscalCode: one FiscalCode 
}

sig Municipality extends User {
	reports: set Report,
	accidents: set Accident,
	area: some Position
}








--Signatures concerning reports

abstract sig Status {}

sig Accepted extends Status {}
sig Refused extends Status {}
sig Evaluating extends Status {}

sig Intervention {}

sig LicensePlate {}

sig Date {}

sig ViolationType {}

sig Photo {}

sig Time {}

sig Position {}

sig HighFrequencyViolationsArea extends Position {}

sig UnsafeArea extends Position {
	possibleSolutions: set Intervention
}

sig Accident {
	position: one Position
}

abstract sig Boolean {}

sig True extends Boolean {}
sig False extends Boolean {}





sig Report {
	idReport: one Int,
	reporter: one Citizen,
	date: one Date,
	time: one Time,
	violationType: one ViolationType,
	photo: one Photo,
	position: one Position,
	status : one Status,
	correspondence: one LicensePlate,
	ticket: one Boolean
} {	
	idReport > 0	
}

sig AcceptedReports {
	acceptedReports: set Report
}



--All Users have different usernames

fact DifferentUsernames {
	all disj u1, u2: User | u1.registration.username != u2.registration.username
}

--All Citizens have different fiscal codes

fact DifferentFiscalCodes {
	all disj c1,c2: Citizen | c1.fiscalCode != c2.fiscalCode
}

--All Usernames match one Registration

fact UsernamesMatchOneRegistration {
	all u: Username | one r: Registration | u in r.username
}



--All Reports made by Citizens are in the list of Reports of the corresponding Municipality

fact ReportsToMunicipalityList {
	all r: Report| one m: Municipality | one c: Citizen | r in m.reports && r in c.reports
}

--All Reports are made by a Citizen registered in the system

fact ReportsHaveRegisteredCitizen {
	all r: Report | one r2: Registration | r.reporter.registration = r2
}

--All Reports which are accepted have a ticket

fact AcceptedReportsHaveTicketTrue {
	all r: Report | ( r.status = Accepted)  <=>  (r.ticket = True)
}

--All Reports which are refused don’t have a ticket

fact RefusedReportsHaveTicketFalse {
	all r: Report | (r.status = Refused)  => (r.ticket = False)
}

--All Reports which are being evaluated don’t have a ticket

 fact EvaluatingReportsHaveTicketFalse {
	all r: Report | (r.status = Evaluating)  => (r.ticket = False)
}

--All Reports have a different ID

fact DifferentReportId {
	all disj r1, r2: Report | r1.idReport != r2.idReport
}



--All Reports with the same Reporter, Position, Time, Date and LicensePlate have the same ID

fact SameReportId {
	all r1, r2: Report | (r1.reporter = r2.reporter && 
r1.correspondence = r2.correspondence && r1.position = r2.position && 
r1.time = r2.time && r1.date = r2.date) <=> r1.idReport = r2.idReport
}

--All accepted Reports are in the set of AcceptedReports

fact AcceptedReportsInSet {
	all r: Report | (r.ticket = True) <=> r in AcceptedReports.acceptedReports
}

--All Report positions belong to the area of one Municipality

fact PositionBelongsToOneArea {
	all r: Report | all m: Municipality | (r.position in m.area) <=> (r in m.reports)
}

--Different Municipalities have different areas with no positions in common

fact DisjAreas {
	all disj m1, m2: Municipality | m1.area & m2.area = none
}

--All Reports are in the list of only one Municipality

fact ReportBelongsToOneMunicipality {
	all r: Report | one m: Municipality | r in m.reports
}

--All Reports with different IDs have different photos

fact DifferentIdDifferentPhoto {
	all r1,r2: Report | (r1.idReport != r2.idReport) <=> (r1.photo != r2.photo)
}


--All Accidents are in the list of the Municipality of their area

fact AccidentsBelongToMunicipalitiesOfSameArea {
	all a: Accident | all m: Municipality | (a in m.accidents) <=> (a.position in m.area)
}

--All positions with more than one accident are marked as unsafe

fact AreasWithManyAccidentsAreUnsafe {
	all m: Municipality | all p: Position | (p in m.area && #{a: Accident | a.position = p} >= 2) <=> p = UnsafeArea
}

--All positions with more than 4 violations are marked as high frequency violations areas

fact AreasWithManyViolationsAreHFA {
	all m: Municipality | all p: Position | (p in m.area && #{r: Report | r.position = p} >= 5) <=> p = HighFrequencyViolationsArea
}



assert CheckNoDifferentMunicipalitiesHaveSameReports {
	all disj m1,m2: Municipality | no r: Report | r in m1.reports && r in m2.reports
}

assert CheckAcceptedReports {
	all r: Report | (r.ticket = True) <=> ( r.status = Accepted 
&& r in AcceptedReports.acceptedReports)
}




pred show {
	#AcceptedReports = 1
	#Citizen = 1
	#Municipality = 1
	#Intervention = 1
}

pred worldOne {
	#Citizen = 2
	#Municipality = 1
	#Report = 2
	#AcceptedReports = 1
	#AcceptedReports.acceptedReports = 1
	(some disj c1, c2: Citizen | one m: Municipality | some disj r1,r2: Report |  r1.reporter = c1 && r2.reporter = c2 &&
	r1.correspondence = r2.correspondence &&
	r1.position != r2.position && r1.date = r2.date && r1.time != r2.time && r1 in m.reports &&
	 r2 in m.reports && r1 in AcceptedReports.acceptedReports && r2  not in AcceptedReports.acceptedReports)

}

pred worldTwo {
	#Citizen = 1
	#Municipality = 2
	#Municipality.area = 3
	#Report = 2
	#AcceptedReports = 1
	(one c: Citizen | some disj m1, m2: Municipality | some disj r1, r2: Report | r1.reporter = c && r2.reporter = c &&
	r1.position in m1.area && r2.position in m2.area && r1.status = Accepted && r2.ticket = False && r1.correspondence != r2.correspondence)
}

pred worldThree {
	#Position = 2
	#Accident = 5
	
}

check CheckAcceptedReports

--check NoDifferentMunicipalitiesTheSameReporting

--run show for 3

--run worldTwo for 3

run worldOne for 3
















