sig Username {}

sig Password {}

sig FiscalCode {}

sig Intervention {}

sig Registration {
	username: one Username,
	password: one Password
}

abstract sig Status {}

sig Accepted extends Status {}

sig Refused extends Status {}

sig Evaluating extends Status {}

sig LicensePlate {}

sig Date {}

sig TypeViolation {}

sig Photo {
}

sig Position {}

sig Time {}

abstract sig Area {
	area: set Position
}

sig HighFrequencyViolationsArea extends Area {
	
}

sig UnsafeArea extends Area {
	
	possibleSolutions: set Intervention
}

abstract sig Boolean {}

sig True extends Boolean {}
sig False extends Boolean {}

sig Reporting {
	idReporting: one Int,
	reporter: one Citizen,
	date: one Date,
	time: one Time,
	typeViolation: one TypeViolation,
	photo: one Photo,
	position: one Position,
	status : one Status,
	correspondence: one LicensePlate,
	ticket: one Boolean
} {	
	idReporting > 0	
}


sig AcceptedReportings {
	acceptedReportings: set Reporting
}

abstract sig User {
	registration: one Registration
}

sig Citizen extends User {
	reportings: set Reporting,
	fiscalCode: one FiscalCode 
}

sig Accident {
	position: one Position
}

sig Municipality extends User {
	reportings: set Reporting,
	accidents: set Accident,
	area: some Position
}

--All Users have different username

fact DifferentUsernames {
	all disj u1, u2: User | u1.registration.username != u2.registration.username
}

--All Citizens have different fiscal codes

fact DifferentFiscalCodes {
	all c1,c2: Citizen | (c1!=c2) => c1.fiscalCode != c2.fiscalCode
}

--All Usernames matches one registration

fact UsernamesMatchesOneRegistration {
	all u: Username | one r: Registration | u in r.username
}

--All reportings made by citizens are in the Municipality list of reportings

fact ReportingsToMunicipalityList {
	all r: Reporting| one m: Municipality | one c: Citizen | r in m.reportings && r in c.reportings
}

--All reportings has a citizen registered in the system

fact ReportingsHasCitizenRegistered {
	all r: Reporting | one r2: Registration | r.reporter.registration = r2
}

--All reportings which has status accepted has also ticket true

fact ReportingStatusTrue {
	all r: Reporting | ( r.status = Accepted)  <=>  (r.ticket = True)
}

--All reportings which has status refused has also ticket false

fact ReportingStatusFalse {
	all r: Reporting | (r.status = Refused)  => (r.ticket = False)
}

--All reportings which has status evaluating  has also ticket false

 fact ReportingStatusEvaluating {
	all r: Reporting | (r.status = Evaluating)  => (r.ticket = False)
}

--All reportings has different Id

fact DifferentId {
	all r1, r2: Reporting | (r1 != r2) => (r1.idReporting != r2.idReporting)
}

--All reportings with the same reporter, position, time, date and license plate have the same Id

fact SameId {
	all r1, r2: Reporting | (r1.reporter = r2.reporter && r1.correspondence = r2.correspondence && r1.position = r2.position && r1.time = r2.time && r1.date = r2.date) 
	<=> r1.idReporting = r2.idReporting
}

--All accepted reportings are in AcceptedReportings' set

fact AcceptedReportingsInSet {
	all r: Reporting | (r.ticket = True) <=> r in AcceptedReportings.acceptedReportings
}

--All reportings' positions belong to one Municipality's area (All m:Municipality o one m:Municipality?) 

fact PositionArea {
	all r: Reporting | all m: Municipality | (r.position in m.area) <=> (r in m.reportings)
}

--Different Municipalities has different areas with no positions in common

fact DisjAreas {
	all disj m1, m2: Municipality | m1.area & m2.area = none
}

--All reportings refer to only one Municipality

fact ReportBelongsToOneMunicipality {
	all r: Reporting | one m: Municipality | r in m.reportings
}

--All reportings with different Id has also different photo

fact DifferentIdDifferentPhoto {
	all r1,r2: Reporting | (r1.idReporting != r2.idReporting) <=> (r1.photo != r2.photo)
}

--All Areas has different positions 

fact DifferentAreas {
	all disj a1, a2: Area | a1.area & a2.area = none
}



fact AccidentsBelongToMunicipalitiesOfSameArea {
	all a: Accident | one m: Municipality | (a in m.accidents) <=> (a.position in m.area)
}

fact AreasWithManyAccidentsAreUnsafe {
	
	all a: Area |  (#{ac: Accident| ac.position in a.area} >=2) <=> a=UnsafeArea
}

fact AreasWithManyViolationsAreHFA {
	all a: Area  | (#{r: Reporting | r.position in a.area}>=2) <=> a= HighFrequencyViolationsArea
}

--No different Municipalities receive the same reporting

assert NoDifferentMunicipalitiesTheSameReporting {
	all disj m1,m2 : Municipality | no r: Reporting | r in m1.reportings && r in m2.reportings
}

assert CheckAcceptedReportings {
	all r : Reporting | all aR: AcceptedReportings | (r.ticket = True) <=> ( r.status = Accepted && r in aR.acceptedReportings)
}

pred show {
	#AcceptedReportings = 1
	#Citizen = 1
	#Municipality = 1
	#Intervention = 1
}

pred worldOne {
	#Citizen = 2
	#Municipality = 1
	#Reporting = 2
	#AcceptedReportings = 1
	#AcceptedReportings.acceptedReportings = 1
	(some disj c1, c2: Citizen | one m: Municipality | some disj r1,r2: Reporting |  r1.reporter = c1 && r2.reporter = c2 &&
	r1.correspondence = r2.correspondence &&
	r1.position != r2.position && r1.date = r2.date && r1.time != r2.time && r1 in m.reportings &&
	 r2 in m.reportings && r1 in AcceptedReportings.acceptedReportings && r2  not in AcceptedReportings.acceptedReportings)

}

pred worldTwo {
	#Citizen = 1
	#Municipality = 2
	#Municipality.area = 3
	#Reporting = 2
	#AcceptedReportings = 1
	(one c: Citizen | some disj m1, m2: Municipality | some disj r1, r2: Reporting | r1.reporter = c && r2.reporter = c &&
	r1.position in m1.area && r2.position in m2.area && r1.status = Accepted && r2.ticket = False && r1.correspondence != r2.correspondence)
}



--check NoDifferentMunicipalitiesTheSameReporting

--run show for 3

run worldTwo for 3

--run worldOne for 3
