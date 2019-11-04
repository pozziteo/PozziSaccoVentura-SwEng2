sig Username {}

sig Password {}

sig FiscalCode {}

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
	licensePlate: one LicensePlate
}
sig Position {}
sig Time {}



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
	ticket: one Boolean
}

abstract sig User {
	registration: one Registration
}



sig Citizen extends User {
	reportings: set Reporting,
	fiscalCode: one FiscalCode 
}

sig Municipality extends User {
	reportings: set Reporting
}

--All Users have different username

fact DifferentUsernames {
	all u1, u2: User | (u1 != u2) => u1.registration.username != u2.registration.username
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
	all r: Reporting | (r.status = Refused)  <=> (r.ticket = False)
}

--All reportings which has status evaluating  has also ticket false

 fact ReportingStatusEvaluating {
	all r: Reporting | (r.status = Evaluating)  <=> (r.ticket = False)
}

--All reportings has different Id

fact DifferentId {
	all r1, r2: Reporting | (r1 != r2) <=> (r1.idReporting != r2.idReporting)
}

--All reportings with the same reporter, position, time, date and license plate have the same Id

fact SameId {
	all r1, r2: Reporting | (r1.reporter = r2.reporter && r1.photo.licensePlate = r2.photo.licensePlate && r1.position = r2.position && r1.time = r2.time && r1.date = r2.date) 
	<=> r1.idReporting = r2.idReporting
}

--All reportings with the same position, time, date and license plate has only one ticket

fact CountAsOne {
	all r1,r2: Reporting | (r1.idReporting != r2.idReporting && r1.photo.licensePlate = r2.photo.licensePlate && r1.position = r2.position && r1.time = r2.time && r1.date = r2.date)
	<=> ((r1.ticket = True && r2.ticket = False) || (r1.ticket = False && r2.ticket = True))
}

--All reportings are pointed out by one user once

fact UserReportsOnce {
	all r1 , r2: Reporting | (r1.position = r2.position && r1.photo.licensePlate = r2.photo.licensePlate) => r1.reporter != r2.reporter 
}

--No different Municipalities receive the same reporting

assert NoDifferentMunicipalitiesTheSameReporting {
	all m1,m2 : Municipality | no r: Reporting | r in m1.reportings && r in m2.reportings && m1 = m2
}

check NoDifferentMunicipalitiesTheSameReporting for 3

pred firstOne {
	#Municipality = 2	
	#Citizen = 5	
 	
	(all m: Municipality | some c: Citizen | some r: Reporting | r in m.reportings && r.reporter = c)
}


run firstOne for 2 Municipality















